module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import stacks_project.Chap06.Example_6_4_5
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat
open TopCat.Presheaf

universe u v

noncomputable section

variable {X : TopCat.{u}}

/- Domain-style sampling for Example 6.7.6:
- primary domain: sheaf conditions for presheaves of sections on a topological space;
- sampled owner API:
  `TopCat.PrelocalPredicate`,
  `TopCat.LocalPredicate`,
  `TopCat.subpresheafToTypes`,
  `TopCat.subpresheafToTypes.isSheaf`;
- source/core/bridge triage:
  `source-facing`: the direct-sum presheaf `U ↦ Π₀ x : U, M x.1`;
  `core/canonical`: the subsheaf-of-functions owner supplied by `subpresheafToTypes`;
  `bridge/view`: the comparison isomorphism identifying a `DFinsupp` section with an ordinary
    dependent function whose nonzero locus is finite.

Primitive data for the source-facing object are just ordinary dependent functions together with the
finite-support condition. The `DFinsupp` presentation from `Example_6_4_5` is therefore a concrete
model, while the owner abstraction for the sheaf argument is the canonical subpresheaf of
`TopCat.presheafToTypes` cut out by the finite-support predicate.
-/

section

variable (M : X → Type v) [∀ x, AddCommGroup (M x)]

/-- Ordinary dependent sections on an open set whose nonzero locus is finite. -/
private def pointwiseFiniteSupport {U : Opens X} (s : ∀ x : U, M x.1) : Prop :=
  Set.Finite {x : U | s x ≠ 0}

/-- The finite-support condition is stable under restriction, so it defines a prelocal predicate on
the sheaf of all dependent functions. -/
private def pointwiseFiniteSupportPrelocalPredicate : TopCat.PrelocalPredicate M where
  pred := pointwiseFiniteSupport M
  res := by
    intro U V i s hs
    classical
    simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using
      Set.Finite.preimage_embedding
        ⟨Set.inclusion i.le, fun a b h ↦ by simpa [Set.inclusion] using h⟩ hs

/-- If every open subset of `X` is compact, finite support is a local predicate. -/
private def pointwiseFiniteSupportLocalPredicate
    (hqc : ∀ U : Opens X, IsCompact (U : Set X)) : TopCat.LocalPredicate M where
  toPrelocalPredicate := pointwiseFiniteSupportPrelocalPredicate M
  locality := by
    intro U s hs
    classical
    choose V hxV i hi using hs
    have hi' (x : U) : Set.Finite { y : V x | s (i x y) ≠ 0 } := by
      simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using hi x
    obtain ⟨t, ht⟩ :=
      (hqc U).elim_finite_subcover (fun x : U ↦ (V x : Set X)) (fun x ↦ (V x).isOpen)
        (by
          intro x hx
          exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simpa using hxV ⟨x, hx⟩⟩)
    refine Set.Finite.subset
      (t.finite_toSet.biUnion fun x hx ↦ (hi' x).image (i x)) fun y hy ↦ ?_
    rcases Set.mem_iUnion₂.1 (ht y.2) with ⟨x, hx, hyV⟩
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    refine ⟨⟨y.1, hyV⟩, ?_, ?_⟩
    · simpa using hy
    · ext
      rfl

/-- A `DFinsupp` section is canonically the same thing as an ordinary dependent section with finite
support. -/
private noncomputable def pointwiseDirectSumSectionEquiv (U : Opens X) :
    (Π₀ x : U, M x.1) ≃ { s : ∀ x : U, M x.1 // pointwiseFiniteSupport M s } where
  toFun f := ⟨f, by simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using f.finite_support⟩
  invFun s := by
    classical
    exact DFinsupp.mk s.2.toFinset fun x ↦ s.1 x
  left_inv := by
    classical
    intro f
    let g : ∀ y : ((f.finite_support.toFinset : Finset U) : Set U), M y.1 := fun y ↦ f y.1
    ext x
    change (DFinsupp.mk f.finite_support.toFinset g : Π₀ y : U, M y.1) x = f x
    by_cases hx : f x = 0
    · have hx' : x ∉ f.finite_support.toFinset := by
        rw [Set.Finite.mem_toFinset]
        simp [Set.mem_setOf_eq, hx]
      simp [g, DFinsupp.mk_apply, hx', hx]
    · have hx' : x ∈ f.finite_support.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact hx
      simp [g, DFinsupp.mk_apply, hx']
  right_inv := by
    classical
    intro s
    let g : ∀ y : ((s.2.toFinset : Finset U) : Set U), M y.1 := fun y ↦ s.1 y.1
    apply Subtype.ext
    funext x
    change (DFinsupp.mk s.2.toFinset g : Π₀ y : U, M y.1) x = s.1 x
    by_cases hx : s.1 x = 0
    · have hx' : x ∉ s.2.toFinset := by
        rw [Set.Finite.mem_toFinset]
        simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using hx
      simp [g, DFinsupp.mk_apply, hx', hx]
    · have hx' : x ∈ s.2.toFinset := by
        rw [Set.Finite.mem_toFinset]
        simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using hx
      simp [g, DFinsupp.mk_apply, hx']

/-- The underlying set-valued presheaf of `pointwiseDirectSumPresheaf` is canonically the
subpresheaf of all dependent functions cut out by the finite-support predicate. -/
private noncomputable def pointwiseDirectSumUnderlyingIsoSubpresheaf :
    pointwiseDirectSumPresheaf M ⋙ forget AddCommGrpCat.{max u v} ≅
      subpresheafToTypes (pointwiseFiniteSupportPrelocalPredicate M) :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso (pointwiseDirectSumSectionEquiv M U.unop))
    (by
      intro U V i
      ext f
      rfl)

/-- Under the compact-open hypothesis, the underlying set-valued presheaf of
`pointwiseDirectSumPresheaf` is a sheaf because it is the canonical subsheaf of all dependent
functions satisfying the local finite-support predicate. -/
private theorem pointwiseDirectSumPresheaf_underlying_isSheaf_of_compact_opens
    (hqc : ∀ U : Opens X, IsCompact (U : Set X)) :
    TopCat.Presheaf.IsSheaf (pointwiseDirectSumPresheaf M ⋙ forget AddCommGrpCat.{max u v}) := by
  exact
    (isSheaf_iso_iff (pointwiseDirectSumUnderlyingIsoSubpresheaf M)).2 <|
      subpresheafToTypes.isSheaf (pointwiseFiniteSupportLocalPredicate M hqc)

/-- Example 6.7.6: if every open subset of `X` is quasi-compact, then the pointwise direct-sum
presheaf from Example 6.4.5 satisfies the sheaf condition. -/
theorem pointwiseDirectSumPresheaf_isSheaf_of_compact_opens
    (hqc : ∀ U : Opens X, IsCompact (U : Set X)) :
    (pointwiseDirectSumPresheaf M).IsSheaf := by
  exact
    (isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat.{max u v}) (pointwiseDirectSumPresheaf M)).2 <|
      pointwiseDirectSumPresheaf_underlying_isSheaf_of_compact_opens M hqc

-- Proof sketch: on an infinite discrete space, the singleton open cover identifies the sheaf
-- condition with an infinite product, while `pointwiseDirectSumPresheaf` uses the direct sum.
/-- Helper for Example 6.7.6: a direct-sum section on `⊤` that is equal to `1` at every point has
infinite support, so it cannot come from `DFinsupp`. -/
private lemma global_support_infinite_of_all_ones [Infinite X] (t : Π₀ _ : (⊤ : Opens X), ℤ)
    (ht : ∀ x : X, t ⟨x, by trivial⟩ = 1) :
    ¬ Set.Finite {y : (⊤ : Opens X) | t y ≠ 0} := by
  intro hsupport
  let e : X ↪ {y : (⊤ : Opens X) | t y ≠ 0} :=
    ⟨fun x ↦ ⟨⟨x, by trivial⟩, by simp [ht x]⟩, fun x y hxy ↦ by
      simpa using congrArg (fun z : {y : (⊤ : Opens X) | t y ≠ 0} => z.1.1) hxy⟩
  have : Finite {y : (⊤ : Opens X) | t y ≠ 0} := hsupport.to_subtype
  have : Finite X := Finite.of_injective e e.injective
  exact not_finite X

/-- Companion to Example 6.7.6: on an infinite discrete space, the pointwise direct-sum presheaf
with constant fiber `ℤ` does not satisfy the sheaf condition. -/
theorem pointwiseDirectSumPresheaf_not_isSheaf_of_infinite_discrete
    [DiscreteTopology X] [Infinite X] :
    ¬ (pointwiseDirectSumPresheaf (fun _ : X ↦ ℤ)).IsSheaf := by
  classical
  intro hsheaf
  let F := pointwiseDirectSumPresheaf (fun _ : X ↦ ℤ)
  let U : X → Opens X := fun x ↦ ⟨{x}, isOpen_discrete _⟩
  let sf : ∀ x : X, F.obj (Opposite.op (U x)) := fun x ↦
    DFinsupp.single ⟨x, by
      change x ∈ ({x} : Set X)
      simp⟩ (1 : ℤ)
  let Fsh : X.Sheaf AddCommGrpCat := ⟨F, hsheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F U sf := by
    intro x y
    ext z
    -- On a point of `U x ⊓ U y`, both singleton sections evaluate at the unique common point.
    have hz_x : z.1 = x := by
      simpa [U] using z.2.1
    have hz_y : z.1 = y := by
      simpa [U] using z.2.2
    have hleft :
        ((F.map (Opens.infLELeft (U x) (U y)).op) (sf x)) z = 1 := by
      rw [pointwiseDirectSumPresheaf_map_apply]
      have hindex :
          (⟨z, (Opens.infLELeft (U x) (U y)).le z.2⟩ : U x) =
            ⟨x, by
              change x ∈ ({x} : Set X)
              simp⟩ := by
        ext
        exact hz_x
      rw [hindex]
      simp [sf]
    have hright :
        ((F.map (Opens.infLERight (U x) (U y)).op) (sf y)) z = 1 := by
      rw [pointwiseDirectSumPresheaf_map_apply]
      have hindex :
          (⟨z, (Opens.infLERight (U x) (U y)).le z.2⟩ : U y) =
            ⟨y, by
              change y ∈ ({y} : Set X)
              simp⟩ := by
        ext
        exact hz_y
      rw [hindex]
      simp [sf]
    exact hleft.trans hright.symm
  have hcover : (⊤ : Opens X) ≤ iSup U := by
    -- Every point belongs to its own singleton open, so the singleton opens cover `⊤`.
    intro x hx
    simp [U]
  obtain ⟨t, ht, -⟩ := Fsh.existsUnique_gluing' (U := U) (V := (⊤ : Opens X))
    (iUV := fun x ↦ homOfLE (by
      intro y hy
      trivial)) hcover sf hcompat
  have ht_one : ∀ x : X, t ⟨x, by trivial⟩ = 1 := by
    intro x
    -- Evaluating the gluing on the singleton cover recovers the prescribed local section.
    have hx := congrArg (fun g => g ⟨x, by simp [U]⟩) (ht x)
    simpa [Fsh, F, sf, U] using hx
  -- The glued section is everywhere `1`, hence has infinite support, contradicting `DFinsupp`.
  exact global_support_infinite_of_all_ones t ht_one t.finite_support

end
