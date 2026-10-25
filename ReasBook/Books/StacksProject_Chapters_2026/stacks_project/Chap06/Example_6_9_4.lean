module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafOfFunctions


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v uC

/- Domain-style sampling for Example 6.9.4:
- primary domain: sheaf conditions for `TopCat`-valued product presheaves on a discrete base and
  for the discrete-topology bridge obtained from the underlying type-valued owner;
- sampled owner API:
  `TopCat.presheafToTypes`,
  `TopCat.Presheaf.toTypes_isSheaf`,
  `pointwiseProductPresheaf`,
  `pointwiseProductPresheaf_isSheaf`;
- owner abstraction:
  the set-valued owner is the dependent-function presheaf `TopCat.presheafToTypes (TopCat.of ℕ) A`;
  the topological-space owner for the product-topology version is the chapter-level canonical
  `pointwiseProductPresheaf` specialized to the discrete fibers `TopCat.discrete.obj (A i)`;
  the sectionwise-discrete topology is only the bridge/view given by composition with
  `TopCat.discrete`;
- primitive-vs-derived split:
  primitive data are only the fibres `A : ℕ → Type v`;
  the product-topology presheaf is derived from the canonical `TopCat` product owner
  `pointwiseProductPresheaf`, the underlying set-valued sheaf condition is derived from
  `TopCat.Presheaf.toTypes_isSheaf`, and the sheaf failure is attached only to the
  discrete-topology bridge;
- source/core/bridge triage:
  `source-facing`: the contrast that the product-topology presheaf is a sheaf of topological
    spaces, while the sectionwise-discrete-topology realization has a sheaf underlying presheaf of
    sets but is not itself a sheaf when each fibre has at least two elements;
  `core/canonical`: `TopCat.presheafToTypes` for the underlying set-valued owner and
    `pointwiseProductPresheaf` for the `TopCat`-valued product-topology owner;
  `bridge/view`: composition with `TopCat.discrete`.

The file should therefore reuse the chapter owner `pointwiseProductPresheaf` for the positive
topological statement, and use `TopCat.presheafToTypes` only for the underlying set-valued bridge
of the sectionwise-discrete presheaf.
-/

section

variable (A : ℕ → Type v)

section PointwiseProductPresheaf

open CategoryTheory.Limits

variable {X : TopCat.{u}} {C : Type v} [Category.{uC} C] [HasProducts.{u} C]

/-- Helper for Example 6.9.4: the canonical presheaf whose section over an open set `U` is the
product of the fibers over the points of `U`. -/
def pointwiseProductPresheaf (Aₓ : X → C) : TopCat.Presheaf C X where
  obj U := ∏ᶜ fun x : U.unop ↦ Aₓ x.1
  map {_ _} i := Pi.map' i.unop (fun _ ↦ 𝟙 _)
  map_id U := by
    -- The identity restriction leaves every coordinate unchanged.
    simp
  map_comp {U V W} i j := by
    -- Restricting along a composite inclusion is the same as restricting twice.
    simpa using
      (Pi.map'_comp_map' i.unop j.unop (fun _ ↦ 𝟙 _) (fun _ ↦ 𝟙 _)).symm

end PointwiseProductPresheaf

/-- Helper for Example 6.9.4: the singleton-open cover of the discrete space `ℕ`. -/
abbrev singleton_cover : ℕ → TopologicalSpace.Opens (TopCat.of ℕ) :=
  fun n ↦ ⟨{n}, isOpen_discrete _⟩

/-- Helper for Example 6.9.4: the presheaf obtained by endowing each section space of
`TopCat.presheafToTypes` with the discrete topology. -/
abbrev sectionwise_discrete_presheaf : TopCat.Presheaf TopCat (TopCat.of ℕ) :=
  (((TopCat.of ℕ).presheafToTypes A) ⋙ TopCat.discrete)

/-- Helper for Example 6.9.4: the `TopCat`-valued presheaf whose fibres are the discrete spaces
`A i` and whose sections carry the product topology. -/
abbrev discreteFiberProductPresheaf : TopCat.Presheaf TopCat (TopCat.of ℕ) :=
  pointwiseProductPresheaf
    (fun i : TopCat.of ℕ ↦ (TopCat.discrete.obj (A i) : TopCat.{v}))

-- The next helper suite prepares the positive sheaf statement by identifying the underlying
-- dependent-function presheaf and the actual function-space topology of restrictions to a cover.
/-- Helper for Example 6.9.4: over an open set `U`, the underlying type of the product-topology
section space is canonically the dependent function type on `U`. -/
private noncomputable abbrev pointwiseProductPresheafCompForgetComponentIso
    (U : (TopologicalSpace.Opens (TopCat.of ℕ))ᵒᵖ) :
    ((discreteFiberProductPresheaf A ⋙ forget TopCat).obj U) ≅
      (((TopCat.of ℕ).presheafToTypes A).obj U) :=
  (forget TopCat).mapIso
    (TopCat.piIsoPi (fun x : U.unop ↦ (TopCat.discrete.obj (A x.1) : TopCat.{v})))

/-- Helper for Example 6.9.4: the component comparison commutes with restriction maps by tracking
one chosen coordinate of the section. -/
private theorem pointwiseProductPresheafCompForget_coordinate_naturality
    {U V : (TopologicalSpace.Opens (TopCat.of ℕ))ᵒᵖ} (i : U ⟶ V)
    (s : (discreteFiberProductPresheaf A ⋙ forget TopCat).obj U)
    (x : V.unop) :
    (pointwiseProductPresheafCompForgetComponentIso (A := A) V).hom
        ((discreteFiberProductPresheaf A ⋙ forget TopCat).map i s) x =
      (pointwiseProductPresheafCompForgetComponentIso (A := A) U).hom s
        ⟨x.1, i.unop.le x.2⟩ := by
  -- Rewrite both sides through `TopCat.piIsoPi`, then evaluate the `Pi.map'` restriction at the
  -- chosen coordinate.
  rw [show
      (pointwiseProductPresheafCompForgetComponentIso (A := A) V).hom
          ((discreteFiberProductPresheaf A ⋙ forget TopCat).map i s) x =
        (TopCat.piIsoPi (fun y : V.unop ↦ (TopCat.discrete.obj (A y.1) : TopCat.{v}))).hom
          ((discreteFiberProductPresheaf A ⋙ forget TopCat).map i s) x by
      rfl]
  rw [show
      (pointwiseProductPresheafCompForgetComponentIso (A := A) U).hom s
          ⟨x.1, i.unop.le x.2⟩ =
        (TopCat.piIsoPi (fun y : U.unop ↦ (TopCat.discrete.obj (A y.1) : TopCat.{v}))).hom s
          ⟨x.1, i.unop.le x.2⟩ by
      rfl]
  rw [TopCat.piIsoPi_hom_apply, TopCat.piIsoPi_hom_apply]
  let p : V.unop → U.unop := fun y ↦ ⟨y.1, i.unop.le y.2⟩
  have hπ :=
    (Pi.map'_comp_π
      (f := fun y : U.unop ↦ (TopCat.discrete.obj (A y.1) : TopCat.{v}))
      (g := fun y : V.unop ↦ (TopCat.discrete.obj (A y.1) : TopCat.{v}))
      p (fun _ ↦ 𝟙 _) x)
  exact ConcreteCategory.congr_hom hπ s

/-- Helper for Example 6.9.4: forgetting the product-topology presheaf identifies it with the
canonical dependent-function presheaf of sets. -/
private noncomputable abbrev pointwiseProductPresheafCompForgetIsoToTypes :
    (discreteFiberProductPresheaf A ⋙ forget TopCat) ≅
      ((TopCat.of ℕ).presheafToTypes A) :=
  NatIso.ofComponents
    (fun U ↦ pointwiseProductPresheafCompForgetComponentIso (A := A) U)
    (fun {U V} i ↦ by
      -- Evaluate the naturality square on one section and one coordinate.
      ext s
      apply funext
      intro x
      simpa [TopCat.presheafToTypes_map] using
        pointwiseProductPresheafCompForget_coordinate_naturality (A := A) i s x)

/-- Helper for Example 6.9.4: on the actual dependent-function space over `⋃ U i`, the product
topology is the topology induced by the restriction map to the family of sections over the `U i`.
-/
private theorem pointwiseProductPresheaf_discrete_function_topology_eq_induced
    {ι : Type u} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    (Pi.topologicalSpace :
      TopologicalSpace (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1))) =
      (Pi.topologicalSpace :
        TopologicalSpace (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1))).induced
        (fun s i x => s ⟨x.1, (TopologicalSpace.Opens.leSupr U i).le x.2⟩) := by
  let r : (∀ y : ↥(iSup U), TopCat.discrete.obj (A y.1)) →
      (∀ i : ι, ∀ y : ↥(U i), TopCat.discrete.obj (A y.1)) :=
    fun s i y => s ⟨y.1, (TopologicalSpace.Opens.leSupr U i).le y.2⟩
  change Pi.topologicalSpace = TopologicalSpace.induced r Pi.topologicalSpace
  apply le_antisymm
  · -- Restricting a section to each cover member is continuous coordinatewise.
    exact continuous_iff_le_induced.mp (by
      apply continuous_pi
      intro i
      change Continuous fun s : (∀ y : ↥(iSup U), TopCat.discrete.obj (A y.1)) =>
        fun y : ↥(U i) => s ⟨y.1, (TopologicalSpace.Opens.leSupr U i).le y.2⟩
      apply continuous_pi
      intro y
      exact
        continuous_apply (A := fun z : ↥(iSup U) => TopCat.discrete.obj (A z.1))
          ⟨y.1, (TopologicalSpace.Opens.leSupr U i).le y.2⟩)
  · -- Each coordinate of the section over `⋃ U i` is detected on one chosen member of the cover.
    change TopologicalSpace.induced r Pi.topologicalSpace ≤ Pi.topologicalSpace
    change TopologicalSpace.induced r Pi.topologicalSpace ≤
      ⨅ x : ↥(iSup U),
        TopologicalSpace.induced (fun s => s x) (TopCat.discrete.obj (A x.1)).str
    apply le_iInf
    intro x
    rcases TopologicalSpace.Opens.mem_iSup.mp x.2 with ⟨i, hx⟩
    let xi : ↥(U i) := ⟨x.1, hx⟩
    let g :
        (∀ i : ι, ∀ y : ↥(U i), TopCat.discrete.obj (A y.1)) →
          TopCat.discrete.obj (A x.1) := fun t => t i xi
    have hg_le :
        Pi.topologicalSpace ≤ TopologicalSpace.induced g (TopCat.discrete.obj (A x.1)).str := by
      exact continuous_iff_le_induced.mp ((continuous_apply xi).comp (continuous_apply i))
    calc
      TopologicalSpace.induced r Pi.topologicalSpace
          ≤ TopologicalSpace.induced r
              (TopologicalSpace.induced g (TopCat.discrete.obj (A x.1)).str) :=
            induced_mono hg_le
      _ = TopologicalSpace.induced (fun s => g (r s)) (TopCat.discrete.obj (A x.1)).str := by
            rw [induced_compose]
            rfl
      _ = TopologicalSpace.induced (fun s => s x) (TopCat.discrete.obj (A x.1)).str := by
            simp [r, xi, g]

/-- Helper for Example 6.9.4: the section space over `⋃ U i` is canonically the dependent
function space on that union. -/
private noncomputable abbrev pointwiseProductPresheaf_discrete_sourceIso
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    (discreteFiberProductPresheaf A).obj (Opposite.op (iSup U)) ≅
      TopCat.of.{v} (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1)) :=
  TopCat.piIsoPi (fun x : ↥(iSup U) ↦ (TopCat.discrete.obj (A x.1) : TopCat.{v}))

/-- Helper for Example 6.9.4: the equalizer-products object `piOpens` is canonically the iterated
dependent-function space of sections over the cover members. -/
private noncomputable abbrev pointwiseProductPresheaf_discrete_piOpensIso
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
        (ι := ι) (discreteFiberProductPresheaf A) U ≅
      TopCat.of.{v} (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1)) :=
  (TopCat.piIsoPi (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))) ≪≫
    TopCat.isoOfHomeo
      (X := TopCat.of.{v} (∀ i : ι, (discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
      (Y := TopCat.of.{v} (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1)))
      (Homeomorph.piCongrRight fun i ↦
        TopCat.homeoOfIso
          (TopCat.piIsoPi (fun x : ↥(U i) ↦ (TopCat.discrete.obj (A x.1) : TopCat.{v}))))

/-- Helper for Example 6.9.4: the concrete dependent-function restriction is continuous for the
product topologies on the source and target function spaces. -/
private theorem pointwiseProductPresheaf_discrete_functionRes_continuous
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    Continuous fun s : (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1)) =>
      fun i : ι => fun x : ↥(U i) => s ⟨x.1, (TopologicalSpace.Opens.leSupr U i).le x.2⟩ := by
  -- Each target coordinate is just evaluation at one restricted point of `⋃ U i`.
  apply continuous_pi
  intro i
  change Continuous fun s : (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1)) =>
    fun x : ↥(U i) => s ⟨x.1, (TopologicalSpace.Opens.leSupr U i).le x.2⟩
  apply continuous_pi
  intro x
  exact
    continuous_apply
      (A := fun z : ↥(iSup U) => TopCat.discrete.obj (A z.1))
      ⟨x.1, (TopologicalSpace.Opens.leSupr U i).le x.2⟩

/-- Helper for Example 6.9.4: under the canonical function-space identifications, the sheaf
restriction map is the evident dependent-function restriction. -/
private noncomputable abbrev pointwiseProductPresheaf_discrete_functionRes
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    TopCat.of.{v} (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1)) ⟶
      TopCat.of.{v} (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1)) :=
  TopCat.ofHom <|
    ContinuousMap.mk
      (fun s i x ↦ s ⟨x.1, (TopologicalSpace.Opens.leSupr U i).le x.2⟩)
      (pointwiseProductPresheaf_discrete_functionRes_continuous A U)

/-- Helper for Example 6.9.4: evaluating the transported sheaf restriction at one cover index and
one point recovers the corresponding restricted coordinate of the original section. -/
private theorem pointwiseProductPresheaf_discrete_res_transport_coordinate
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ))
    (s : (discreteFiberProductPresheaf A).obj (Opposite.op (iSup U)))
    (i : ι) (x : ↥(U i)) :
    (pointwiseProductPresheafCompForgetComponentIso (A := A) (Opposite.op (U i))).hom
        (((discreteFiberProductPresheaf A ⋙ forget TopCat).map
            ((TopologicalSpace.Opens.leSupr U i).op)) s) x =
      ((pointwiseProductPresheaf_discrete_sourceIso A U).hom s)
        ⟨x.1, (TopologicalSpace.Opens.leSupr U i).le x.2⟩ := by
  -- This is the coordinate naturality statement for the product presheaf, specialized to the
  -- inclusion `U i ⊆ ⋃ U i`.
  simpa using
    pointwiseProductPresheafCompForget_coordinate_naturality
      (A := A) ((TopologicalSpace.Opens.leSupr U i).op) s x

/-- Helper for Example 6.9.4: after identifying source and target with literal function spaces,
the equalizer-products restriction map becomes the concrete dependent-function restriction. -/
private theorem pointwiseProductPresheaf_discrete_res_transport
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    TopCat.Presheaf.SheafConditionEqualizerProducts.res
        (ι := ι) (discreteFiberProductPresheaf A) U ≫
        (pointwiseProductPresheaf_discrete_piOpensIso A U).hom =
      (pointwiseProductPresheaf_discrete_sourceIso A U).hom ≫
        pointwiseProductPresheaf_discrete_functionRes A U := by
  -- Evaluate both maps on a section, then on one cover index and one point of that open.
  ext s i x
  -- The outer `piIsoPi` and inner coordinate isomorphism reduce the categorical restriction to
  -- the already computed coordinate naturality statement.
  change
      ((pointwiseProductPresheaf_discrete_piOpensIso A U).hom
          ((TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A) U) s)) i x =
        (pointwiseProductPresheaf_discrete_functionRes A U)
          ((pointwiseProductPresheaf_discrete_sourceIso A U).hom s) i x
  dsimp [pointwiseProductPresheaf_discrete_piOpensIso,
    pointwiseProductPresheaf_discrete_functionRes]
  change
      ((TopCat.piIsoPi
          (fun y : ↥(U i) ↦ (TopCat.discrete.obj (A y.1) : TopCat.{v}))).hom
          (((TopCat.piIsoPi
              (fun j : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U j)))).hom
              ((TopCat.Presheaf.SheafConditionEqualizerProducts.res
                (ι := ι) (discreteFiberProductPresheaf A) U) s)) i)) x =
        ((pointwiseProductPresheaf_discrete_sourceIso A U).hom s)
          ⟨x.1, (TopologicalSpace.Opens.leSupr U i).le x.2⟩
  rw [TopCat.piIsoPi_hom_apply]
  rw [TopCat.piIsoPi_hom_apply]
  have hres :
      (ConcreteCategory.hom
          (Pi.π
            (fun j : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U j))) i))
          ((ConcreteCategory.hom
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U)) s) =
        ((discreteFiberProductPresheaf A).map ((TopologicalSpace.Opens.leSupr U i).op)) s := by
    simpa using
      ConcreteCategory.congr_hom
        (TopCat.Presheaf.SheafConditionEqualizerProducts.res_π
          (F := discreteFiberProductPresheaf A) (U := U) i)
        s
  rw [hres]
  simpa [pointwiseProductPresheafCompForgetComponentIso, TopCat.piIsoPi_hom_apply] using
    pointwiseProductPresheaf_discrete_res_transport_coordinate (A := A) U s i x

/-- Helper for Example 6.9.4: the object topology on sections over `⋃ U i` is exactly the
topology induced from the equalizer-products restriction morphism. -/
private theorem pointwiseProductPresheaf_discrete_topology_eq_induced_res
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    ((discreteFiberProductPresheaf A).obj (Opposite.op (iSup U))).str =
      (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
          (ι := ι) (discreteFiberProductPresheaf A) U).str.induced
        (TopCat.Presheaf.SheafConditionEqualizerProducts.res
          (ι := ι) (discreteFiberProductPresheaf A) U) := by
  -- First identify the source object with the literal dependent-function space over `⋃ U i`.
  have hsource :
      ((discreteFiberProductPresheaf A).obj (Opposite.op (iSup U))).str =
        TopologicalSpace.induced (pointwiseProductPresheaf_discrete_sourceIso A U).hom
          (TopCat.of.{v} (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1))).str := by
    simpa using
      (TopCat.homeoOfIso (pointwiseProductPresheaf_discrete_sourceIso A U)).induced_eq.symm
  -- Next transport the function-space induced-topology calculation along the source isomorphism.
  have hfunction :
      TopologicalSpace.induced (pointwiseProductPresheaf_discrete_sourceIso A U).hom
          (TopCat.of.{v} (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1))).str =
        TopologicalSpace.induced
          ((pointwiseProductPresheaf_discrete_sourceIso A U).hom ≫
            pointwiseProductPresheaf_discrete_functionRes A U)
          (TopCat.of.{v}
            (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1))).str := by
    -- This is exactly the previously proved induced-topology statement on literal function spaces.
    simpa [pointwiseProductPresheaf_discrete_functionRes, induced_compose] using
      congrArg (TopologicalSpace.induced (pointwiseProductPresheaf_discrete_sourceIso A U).hom)
        (pointwiseProductPresheaf_discrete_function_topology_eq_induced (A := A) U)
  -- Finally rewrite the transported restriction map back to the categorical equalizer-products map.
  have htarget :
      TopologicalSpace.induced (pointwiseProductPresheaf_discrete_piOpensIso A U).hom
          (TopCat.of.{v}
            (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1))).str =
        (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
          (ι := ι) (discreteFiberProductPresheaf A) U).str := by
    simpa using
      (TopCat.homeoOfIso (pointwiseProductPresheaf_discrete_piOpensIso A U)).induced_eq
  calc
    ((discreteFiberProductPresheaf A).obj (Opposite.op (iSup U))).str
        =
          TopologicalSpace.induced (pointwiseProductPresheaf_discrete_sourceIso A U).hom
            (TopCat.of.{v}
              (∀ x : ↥(iSup U), TopCat.discrete.obj (A x.1))).str := hsource
    _ =
          TopologicalSpace.induced
            ((pointwiseProductPresheaf_discrete_sourceIso A U).hom ≫
              pointwiseProductPresheaf_discrete_functionRes A U)
            (TopCat.of.{v}
              (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1))).str := hfunction
    _ =
          TopologicalSpace.induced
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U ≫
              (pointwiseProductPresheaf_discrete_piOpensIso A U).hom)
            (TopCat.of.{v}
              (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1))).str := by
          rw [pointwiseProductPresheaf_discrete_res_transport (A := A) U]
    _ =
          TopologicalSpace.induced
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U)
            (TopologicalSpace.induced (pointwiseProductPresheaf_discrete_piOpensIso A U).hom
              (TopCat.of.{v}
                (∀ i : ι, ∀ x : ↥(U i), TopCat.discrete.obj (A x.1))).str) := by
          rw [induced_compose]
          rfl
    _ =
          (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
              (ι := ι) (discreteFiberProductPresheaf A) U).str.induced
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U) := by
          rw [htarget]

/-- Helper for Example 6.9.4: the equalizer-products fork for the product-topology presheaf is a
limit because the underlying `Type`-valued presheaf is already a sheaf and the source topology is
the induced topology from the restriction map. -/
private theorem pointwiseProductPresheafCompForget_fork_isLimit
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    Nonempty
      (IsLimit
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
          (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)) := by
  -- First take the equalizer-products limit supplied by the known sheaf of dependent functions.
  let hTypes :=
    ((TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
        (((TopCat.of ℕ).presheafToTypes A))).mp
      (TopCat.Presheaf.toTypes_isSheaf (X := TopCat.of ℕ) A)) U |>.some
  -- Then transport that limit along the canonical presheaf isomorphism after forgetting `TopCat`.
  let hPost :=
    (CategoryTheory.Limits.IsLimit.postcomposeInvEquiv
        (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso U
          (pointwiseProductPresheafCompForgetIsoToTypes (A := A)))
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
          (ι := ι) (((TopCat.of ℕ).presheafToTypes A)) U)).symm hTypes
  exact ⟨CategoryTheory.Limits.IsLimit.ofIsoLimit hPost
    (TopCat.Presheaf.SheafConditionEqualizerProducts.fork.isoOfIso U
      (pointwiseProductPresheafCompForgetIsoToTypes (A := A))).symm⟩

/-- Helper for Example 6.9.4: forgetting the equalizer-products restriction map and then applying
the product comparison on `piOpens` gives the set-valued equalizer-products restriction map. -/
private theorem pointwiseProductPresheafCompForget_res_comp_preservesProductIso
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    (forget TopCat).map
        (TopCat.Presheaf.SheafConditionEqualizerProducts.res
          (ι := ι) (discreteFiberProductPresheaf A) U) ≫
      (PreservesProduct.iso (forget TopCat)
        (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom =
        TopCat.Presheaf.SheafConditionEqualizerProducts.res
          (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U := by
  -- Forgetting the lifted restriction map turns the `TopCat`-valued `Pi.lift` into the
  -- underlying set-valued `Pi.lift` on the same restriction family.
  dsimp [TopCat.Presheaf.SheafConditionEqualizerProducts.res]
  simpa [Functor.map_comp] using
    (map_lift_piComparison (forget TopCat)
      (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
      ((discreteFiberProductPresheaf A).obj (Opposite.op (iSup U)))
      (fun i : ι ↦
        (discreteFiberProductPresheaf A).map ((TopologicalSpace.Opens.leSupr U i).op)))

/-- Helper for Example 6.9.4: forgetting the `TopCat` equalizer-products diagram for the
product-topology presheaf identifies it with the equalizer-products diagram of the forgotten
presheaf. -/
private theorem pointwiseProductPresheafCompForget_diagram_left
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    (forget TopCat).map
        (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
          (ι := ι) (discreteFiberProductPresheaf A) U) ≫
      (PreservesProduct.iso (forget TopCat)
        (fun p : ι × ι ↦
          (discreteFiberProductPresheaf A).obj (Opposite.op (U p.1 ⊓ U p.2)))).hom =
        (PreservesProduct.iso (forget TopCat)
          (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
          TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U := by
  -- Check the left restriction square after projecting to one chosen intersection coordinate.
  apply limit.hom_ext
  intro p
  dsimp [TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes]
  funext s
  -- Read the `p.1` coordinate through the preserved product comparison, then restrict to the
  -- intersection `U p.1 ⊓ U p.2`.
  have hπ :
      (((PreservesProduct.iso (forget TopCat)
          (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
            Pi.π
              (fun i : ι ↦
                (forget TopCat).obj ((discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
              (p.1.1)) s) =
        ((forget TopCat).map
          (Pi.π
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
            (p.1.1))) s := by
    simpa [PreservesProduct.iso_hom, CategoryTheory.types_comp_apply] using
      congr_fun
        (piComparison_comp_π (forget TopCat)
          (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i))) (p.1.1))
        s
  have h₁ :
      (((((forget TopCat).map
          (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
            (ι := ι) (discreteFiberProductPresheaf A) U)) ≫
            (PreservesProduct.iso (forget TopCat)
              (fun p : ι × ι ↦
                (discreteFiberProductPresheaf A).obj
                  (Opposite.op (U p.1 ⊓ U p.2)))).hom ≫
            limit.π _ p) s)) =
        ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
          ((U (p.1.1)).infLELeft (U (p.1.2))).op)
          (((forget TopCat).map
            (Pi.π
              (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
              (p.1.1))) s) := by
    have hq :
        Pi.π
            (fun q : ι × ι ↦
              (forget TopCat).obj ((discreteFiberProductPresheaf A).obj
                (Opposite.op (U q.1 ⊓ U q.2))))
            p.1
            (piComparison (forget TopCat)
              (fun q : ι × ι ↦
                (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2)))
              (((forget TopCat).map
                (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                  (ι := ι) (discreteFiberProductPresheaf A) U)) s)) =
          (ConcreteCategory.hom
            (Pi.π
              (fun q : ι × ι ↦
                (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2)))
              p.1))
            (((forget TopCat).map
              (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                (ι := ι) (discreteFiberProductPresheaf A) U)) s) := by
      simpa [PreservesProduct.iso_hom, CategoryTheory.types_comp_apply] using
        congr_fun
          (piComparison_comp_π (forget TopCat)
            (fun q : ι × ι ↦
              (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2))) p.1)
          (((forget TopCat).map
            (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
              (ι := ι) (discreteFiberProductPresheaf A) U)) s)
    have hlift :
        (ConcreteCategory.hom
          (Pi.π
            (fun q : ι × ι ↦
              (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2)))
            p.1))
          (((forget TopCat).map
            (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
              (ι := ι) (discreteFiberProductPresheaf A) U)) s) =
          (ConcreteCategory.hom
            ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
              ((U (p.1.1)).infLELeft (U (p.1.2))).op))
            ((ConcreteCategory.hom
              (Pi.π
                (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
                (p.1.1))) s) := by
      simpa [TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes] using
        ConcreteCategory.congr_hom
          (limit.lift_π
            (c := Fan.mk _
              (fun q : ι × ι ↦
                Pi.π
                    (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
                    q.1 ≫
                  (discreteFiberProductPresheaf A).map ((U q.1).infLELeft (U q.2)).op))
            (j := ⟨p.1⟩))
          s
    exact hq.trans hlift
  have h₂ :
      ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
        ((U (p.1.1)).infLELeft (U (p.1.2))).op)
        (((forget TopCat).map
          (Pi.π
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
            (p.1.1))) s) =
        ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
          ((U (p.1.1)).infLELeft (U (p.1.2))).op)
          ((((PreservesProduct.iso (forget TopCat)
              (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
                Pi.π
                  (fun i : ι ↦
                    (forget TopCat).obj ((discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
                  (p.1.1)) s)) := by
    simpa using congrArg
      (((discreteFiberProductPresheaf A ⋙ forget TopCat).map
        ((U (p.1.1)).infLELeft (U (p.1.2))).op))
      hπ.symm
  have h₃ :
      ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
        ((U (p.1.1)).infLELeft (U (p.1.2))).op)
        ((((PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
              Pi.π
                (fun i : ι ↦
                  (forget TopCat).obj ((discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
                (p.1.1)) s)) =
        (((((PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
              TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U) ≫
            limit.π _ p) s)) := by
    simp [CategoryTheory.types_comp_apply,
      TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes, PreservesProduct.iso_hom]
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Example 6.9.4: the right equalizer-products restriction square is preserved after
forgetting `TopCat`. -/
private theorem pointwiseProductPresheafCompForget_diagram_right
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    (forget TopCat).map
        (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
          (ι := ι) (discreteFiberProductPresheaf A) U) ≫
      (PreservesProduct.iso (forget TopCat)
        (fun p : ι × ι ↦
          (discreteFiberProductPresheaf A).obj (Opposite.op (U p.1 ⊓ U p.2)))).hom =
        (PreservesProduct.iso (forget TopCat)
          (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
          TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U := by
  -- Check the right restriction square after projecting to one chosen intersection coordinate.
  apply limit.hom_ext
  intro p
  dsimp [TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes]
  funext s
  -- Read the `p.2` coordinate through the preserved product comparison, then restrict to the
  -- same intersection from the right side.
  have hπ :
      (((PreservesProduct.iso (forget TopCat)
          (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
            Pi.π
              (fun i : ι ↦
                (forget TopCat).obj ((discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
              (p.1.2)) s) =
        ((forget TopCat).map
          (Pi.π
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
            (p.1.2))) s := by
    simpa [PreservesProduct.iso_hom, CategoryTheory.types_comp_apply] using
      congr_fun
        (piComparison_comp_π (forget TopCat)
          (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i))) (p.1.2))
        s
  have h₁ :
      (((((forget TopCat).map
          (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
            (ι := ι) (discreteFiberProductPresheaf A) U)) ≫
            (PreservesProduct.iso (forget TopCat)
              (fun p : ι × ι ↦
                (discreteFiberProductPresheaf A).obj
                  (Opposite.op (U p.1 ⊓ U p.2)))).hom ≫
            limit.π _ p) s)) =
        ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
          ((U (p.1.1)).infLERight (U (p.1.2))).op)
          (((forget TopCat).map
            (Pi.π
              (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
              (p.1.2))) s) := by
    have hq :
        Pi.π
            (fun q : ι × ι ↦
              (forget TopCat).obj ((discreteFiberProductPresheaf A).obj
                (Opposite.op (U q.1 ⊓ U q.2))))
            p.1
            (piComparison (forget TopCat)
              (fun q : ι × ι ↦
                (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2)))
              (((forget TopCat).map
                (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
                  (ι := ι) (discreteFiberProductPresheaf A) U)) s)) =
          (ConcreteCategory.hom
            (Pi.π
              (fun q : ι × ι ↦
                (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2)))
              p.1))
            (((forget TopCat).map
              (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
                (ι := ι) (discreteFiberProductPresheaf A) U)) s) := by
      simpa [PreservesProduct.iso_hom, CategoryTheory.types_comp_apply] using
        congr_fun
          (piComparison_comp_π (forget TopCat)
            (fun q : ι × ι ↦
              (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2))) p.1)
          (((forget TopCat).map
            (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
              (ι := ι) (discreteFiberProductPresheaf A) U)) s)
    have hlift :
        (ConcreteCategory.hom
          (Pi.π
            (fun q : ι × ι ↦
              (discreteFiberProductPresheaf A).obj (Opposite.op (U q.1 ⊓ U q.2)))
            p.1))
          (((forget TopCat).map
            (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
              (ι := ι) (discreteFiberProductPresheaf A) U)) s) =
          (ConcreteCategory.hom
            ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
              ((U (p.1.1)).infLERight (U (p.1.2))).op))
            ((ConcreteCategory.hom
              (Pi.π
                (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
                (p.1.2))) s) := by
      simpa [TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes] using
        ConcreteCategory.congr_hom
          (limit.lift_π
            (c := Fan.mk _
              (fun q : ι × ι ↦
                Pi.π
                    (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
                    q.2 ≫
                  (discreteFiberProductPresheaf A).map ((U q.1).infLERight (U q.2)).op))
            (j := ⟨p.1⟩))
          s
    exact hq.trans hlift
  have h₂ :
      ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
        ((U (p.1.1)).infLERight (U (p.1.2))).op)
        (((forget TopCat).map
          (Pi.π
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))
            (p.1.2))) s) =
        ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
          ((U (p.1.1)).infLERight (U (p.1.2))).op)
          ((((PreservesProduct.iso (forget TopCat)
              (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
                Pi.π
                  (fun i : ι ↦
                    (forget TopCat).obj ((discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
                  (p.1.2)) s)) := by
    simpa using congrArg
      (((discreteFiberProductPresheaf A ⋙ forget TopCat).map
        ((U (p.1.1)).infLERight (U (p.1.2))).op))
      hπ.symm
  have h₃ :
      ((discreteFiberProductPresheaf A ⋙ forget TopCat).map
        ((U (p.1.1)).infLERight (U (p.1.2))).op)
        ((((PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
              Pi.π
                (fun i : ι ↦
                  (forget TopCat).obj ((discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
                (p.1.2)) s)) =
        (((((PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
              TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
                (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U) ≫
            limit.π _ p) s)) := by
    simp [CategoryTheory.types_comp_apply,
      TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes, PreservesProduct.iso_hom]
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Example 6.9.4: forgetting the `TopCat` equalizer-products diagram for the
product-topology presheaf identifies it with the equalizer-products diagram of the forgotten
presheaf. -/
private noncomputable abbrev pointwiseProductPresheafCompForget_diagram_iso
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    ((TopCat.Presheaf.SheafConditionEqualizerProducts.diagram
      (ι := ι) (discreteFiberProductPresheaf A) U) ⋙ forget TopCat) ≅
      TopCat.Presheaf.SheafConditionEqualizerProducts.diagram
        (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U :=
  parallelPair.ext
    (PreservesProduct.iso (forget TopCat)
      (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i))))
    (PreservesProduct.iso (forget TopCat)
      (fun p : ι × ι ↦
        (discreteFiberProductPresheaf A).obj (Opposite.op (U p.1 ⊓ U p.2))))
    (pointwiseProductPresheafCompForget_diagram_left (A := A) U)
    (pointwiseProductPresheafCompForget_diagram_right (A := A) U)

/-- Helper for Example 6.9.4: the zero projection of the forgotten `TopCat` fork matches the zero
projection of the postcomposed forgotten-presheaf fork. -/
private theorem pointwiseProductPresheafCompForget_mapCone_fork_π_zero
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    ((forget TopCat).mapCone
      (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
        (ι := ι) (discreteFiberProductPresheaf A) U)).π.app WalkingParallelPair.zero =
      ((Cone.postcompose
        (pointwiseProductPresheafCompForget_diagram_iso (A := A) (ι := ι) U).inv).obj
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
          (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)).π.app
        WalkingParallelPair.zero := by
  -- Compare both zero projections after composing with the product comparison isomorphism on
  -- `piOpens`; the resulting equality is the already established restriction comparison.
  apply (cancel_mono
    (PreservesProduct.iso (forget TopCat)
      (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom).1
  have hres :=
    pointwiseProductPresheafCompForget_res_comp_preservesProductIso (A := A) (ι := ι) U
  have hpost :
      TopCat.Presheaf.SheafConditionEqualizerProducts.res
          (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U =
        ((Cone.postcompose
          (pointwiseProductPresheafCompForget_diagram_iso (A := A) (ι := ι) U).inv).obj
          (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)).π.app
          WalkingParallelPair.zero ≫
          (PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom := by
    rw [Cone.postcompose_obj_π, NatTrans.comp_app,
      TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_zero]
    change
      TopCat.Presheaf.SheafConditionEqualizerProducts.res
          (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U =
        TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U ≫
          (PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).inv ≫
          (PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom
    simpa [Category.assoc] using
      (congrArg
        (fun k =>
          TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U ≫ k)
        ((PreservesProduct.iso (forget TopCat)
          (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).inv_hom_id)).symm
  exact hres.trans hpost

/-- Helper for Example 6.9.4: the one projection of the forgotten `TopCat` fork matches the one
projection of the postcomposed forgotten-presheaf fork. -/
private theorem pointwiseProductPresheafCompForget_mapCone_fork_π_one
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    ((forget TopCat).mapCone
      (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
        (ι := ι) (discreteFiberProductPresheaf A) U)).π.app WalkingParallelPair.one =
      ((Cone.postcompose
        (pointwiseProductPresheafCompForget_diagram_iso (A := A) (ι := ι) U).inv).obj
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
          (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)).π.app
        WalkingParallelPair.one := by
  -- Compare both one projections after composing with the product comparison isomorphism on
  -- `piInters`, then rewrite the left branch by the diagram square proved above.
  apply (cancel_mono
    (PreservesProduct.iso (forget TopCat)
      (fun p : ι × ι ↦
        (discreteFiberProductPresheaf A).obj (Opposite.op (U p.1 ⊓ U p.2)))).hom).1
  simp only [Functor.mapCone_π_app, Cone.postcompose_obj_π,
    TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_one]
  have hstep1 :
      (forget TopCat).map
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A) U) ≫
          (forget TopCat).map
            (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
              (ι := ι) (discreteFiberProductPresheaf A) U) ≫
          (PreservesProduct.iso (forget TopCat)
            (fun p : ι × ι ↦
              (discreteFiberProductPresheaf A).obj (Opposite.op (U p.1 ⊓ U p.2)))).hom
        =
          (forget TopCat).map
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U) ≫
            ((PreservesProduct.iso (forget TopCat)
              (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
              TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U) := by
    simpa [Category.assoc] using
      congrArg
        (fun k =>
          (forget TopCat).map
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U) ≫ k)
        (pointwiseProductPresheafCompForget_diagram_left (A := A) (ι := ι) U)
  have hstep2 :
      (forget TopCat).map
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A) U) ≫
          ((PreservesProduct.iso (forget TopCat)
            (fun i : ι ↦ (discreteFiberProductPresheaf A).obj (Opposite.op (U i)))).hom ≫
            TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
              (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)
        =
          TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U ≫
            TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
              (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U := by
    rw [← Category.assoc,
      pointwiseProductPresheafCompForget_res_comp_preservesProductIso
        (A := A) (ι := ι) U]
    rfl
  exact hstep1.trans <|
    hstep2.trans <|
      by
        simpa [Category.assoc] using
          (congrArg
            (fun k =>
              TopCat.Presheaf.SheafConditionEqualizerProducts.res
                  (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U ≫
                TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                  (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U ≫
                k)
            ((PreservesProduct.iso (forget TopCat)
              (fun p : ι × ι ↦
                (discreteFiberProductPresheaf A).obj (Opposite.op (U p.1 ⊓ U p.2)))).inv_hom_id)).symm

/-- Helper for Example 6.9.4: the forgotten `TopCat` fork and the postcomposed
forgotten-presheaf fork have the same cone projections over the forgotten diagram. -/
private theorem pointwiseProductPresheafCompForget_mapCone_fork_π
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    ∀ j : WalkingParallelPair,
      ((forget TopCat).mapCone
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
          (ι := ι) (discreteFiberProductPresheaf A) U)).π.app j =
        ((Cone.postcompose
          (pointwiseProductPresheafCompForget_diagram_iso (A := A) (ι := ι) U).inv).obj
          (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)).π.app j
  | WalkingParallelPair.zero =>
      pointwiseProductPresheafCompForget_mapCone_fork_π_zero (A := A) (ι := ι) U
  | WalkingParallelPair.one =>
      pointwiseProductPresheafCompForget_mapCone_fork_π_one (A := A) (ι := ι) U

/-- Helper for Example 6.9.4: forgetting the `TopCat` equalizer-products fork yields the same
underlying cone as the forgotten-presheaf fork after postcomposing by the preserved-products
diagram comparison. -/
private noncomputable abbrev pointwiseProductPresheafCompForget_mapCone_fork_iso
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    ((forget TopCat).mapCone
      (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
        (ι := ι) (discreteFiberProductPresheaf A) U)) ≅
      (Cone.postcompose
        (pointwiseProductPresheafCompForget_diagram_iso (A := A) (ι := ι) U).inv).obj
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
          (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U) :=
  Cone.ext (Iso.refl _)
    (pointwiseProductPresheafCompForget_mapCone_fork_π (A := A) (ι := ι) U)

/-- Helper for Example 6.9.4: the equalizer-products fork for the product-topology presheaf is a
limit because the underlying `Type`-valued presheaf is already a sheaf and the source topology is
the induced topology from the restriction map. -/
private theorem pointwiseProductPresheaf_discrete_fork_isLimit
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of ℕ)) :
    Nonempty
      (IsLimit (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
        (ι := ι) (discreteFiberProductPresheaf A) U)) := by
  -- First transport the already proved `Type`-valued limit onto the forgotten `TopCat` fork.
  let hPost :
      IsLimit
        ((Cone.postcompose
          (pointwiseProductPresheafCompForget_diagram_iso (A := A) (ι := ι) U).inv).obj
          (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
            (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)) :=
    (CategoryTheory.Limits.IsLimit.postcomposeInvEquiv
      (pointwiseProductPresheafCompForget_diagram_iso (A := A) (ι := ι) U)
      (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
        (ι := ι) (discreteFiberProductPresheaf A ⋙ forget TopCat) U)).symm
      (pointwiseProductPresheafCompForget_fork_isLimit (A := A) U).some
  let hForget :
      IsLimit
        ((forget TopCat).mapCone
          (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
            (ι := ι) (discreteFiberProductPresheaf A) U)) :=
    CategoryTheory.Limits.IsLimit.ofIsoLimit hPost
      (pointwiseProductPresheafCompForget_mapCone_fork_iso (A := A) (ι := ι) U).symm
  -- Then apply the `TopCat` induced-topology criterion and collapse the infimum to the `res`
  -- branch using continuity of `leftRes`.
  refine (TopCat.nonempty_isLimit_iff_eq_induced
    (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
      (ι := ι) (discreteFiberProductPresheaf A) U) hForget).2 ?_
  have hleft_le :
      (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
        (ι := ι) (discreteFiberProductPresheaf A) U).str ≤
        (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters
          (ι := ι) (discreteFiberProductPresheaf A) U).str.induced
          (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
            (ι := ι) (discreteFiberProductPresheaf A) U) := by
    -- The left restriction map is a morphism in `TopCat`, hence continuous.
    exact continuous_iff_le_induced.mp
      (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
        (ι := ι) (discreteFiberProductPresheaf A) U).hom.continuous
  have hzero_le_one :
      ((TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
        (ι := ι) (discreteFiberProductPresheaf A) U).str.induced
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A) U)) ≤
        ((TopCat.Presheaf.SheafConditionEqualizerProducts.piInters
          (ι := ι) (discreteFiberProductPresheaf A) U).str.induced
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U ≫
              TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                (ι := ι) (discreteFiberProductPresheaf A) U)) := by
    -- Inducing along `res` preserves the order relation coming from continuity of `leftRes`.
    calc
      TopologicalSpace.induced
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A) U)
          (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
            (ι := ι) (discreteFiberProductPresheaf A) U).str
          ≤
            TopologicalSpace.induced
              (TopCat.Presheaf.SheafConditionEqualizerProducts.res
                (ι := ι) (discreteFiberProductPresheaf A) U)
              ((TopCat.Presheaf.SheafConditionEqualizerProducts.piInters
                (ι := ι) (discreteFiberProductPresheaf A) U).str.induced
                (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                  (ι := ι) (discreteFiberProductPresheaf A) U)) :=
          induced_mono hleft_le
      _ =
            ((TopCat.Presheaf.SheafConditionEqualizerProducts.piInters
              (ι := ι) (discreteFiberProductPresheaf A) U).str.induced
                (TopCat.Presheaf.SheafConditionEqualizerProducts.res
                  (ι := ι) (discreteFiberProductPresheaf A) U ≫
                  TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
                    (ι := ι) (discreteFiberProductPresheaf A) U)) := by
          rw [induced_compose]
          rfl
  -- The `WalkingParallelPair.zero` branch is exactly the already computed restriction-induced
  -- topology on the section space over `⋃ U i`.
  have hpt_eq_zero :
      (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
        (ι := ι) (discreteFiberProductPresheaf A) U).pt.str =
        TopologicalSpace.induced
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (ι := ι) (discreteFiberProductPresheaf A) U)
          (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
            (ι := ι) (discreteFiberProductPresheaf A) U).str := by
    simpa [TopCat.Presheaf.SheafConditionEqualizerProducts.fork_pt] using
      pointwiseProductPresheaf_discrete_topology_eq_induced_res (A := A) U
  calc
    (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
      (ι := ι) (discreteFiberProductPresheaf A) U).pt.str
        =
          TopologicalSpace.induced
            (TopCat.Presheaf.SheafConditionEqualizerProducts.res
              (ι := ι) (discreteFiberProductPresheaf A) U)
            (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
              (ι := ι) (discreteFiberProductPresheaf A) U).str := hpt_eq_zero
    _ =
          ⨅ j,
            TopologicalSpace.induced
              ((TopCat.Presheaf.SheafConditionEqualizerProducts.fork
                (ι := ι) (discreteFiberProductPresheaf A) U).π.app j)
              ((TopCat.Presheaf.SheafConditionEqualizerProducts.diagram
                (ι := ι) (discreteFiberProductPresheaf A) U).obj j).str := by
          apply le_antisymm
          · apply le_iInf
            intro j
            cases j using WalkingParallelPair.casesOn
            · exact le_rfl
            · simpa [TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_one]
                using hzero_le_one
          · exact iInf_le _ WalkingParallelPair.zero

-- Proof sketch: transfer the underlying `Type`-valued sheaf condition across the canonical
-- presheaf isomorphism, then transport the actual function-space induced-topology statement back
-- to the `TopCat` product objects.
/-- Example 6.9.4 (1): endowing each fibre `A i` with the discrete topology and each section space
`U ↦ ∏ i : U, A i` with the induced product topology gives a sheaf of topological spaces. This is
the source-facing positive sheaf statement on the canonical owner `pointwiseProductPresheaf`. -/
theorem pointwiseProductPresheaf_discrete_isSheaf :
    (pointwiseProductPresheaf
      (fun i : TopCat.of ℕ ↦ (TopCat.discrete.obj (A i) : TopCat.{v}))).IsSheaf := by
  -- Route correction: the remaining step is to express the `TopCat` equalizer-products fork in
  -- the same literal function-space coordinates as the already-proved induced-topology lemma.
  rw [TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts]
  intro ι U
  -- Once the function-space transport is in place, the equalizer-products fork is a limit.
  exact pointwiseProductPresheaf_discrete_fork_isLimit A U

/-- Example 6.9.4 (2): after equipping each section space `U ↦ ∏ i : U, A i` with the discrete
topology, the underlying presheaf of sets is still the canonical dependent-function sheaf. -/
-- Proof sketch: identify the underlying presheaf of sets with `TopCat.presheafToTypes` and apply
-- `TopCat.Presheaf.toTypes_isSheaf`.
theorem presheafToTypes_discrete_underlying_isSheaf :
    TopCat.Presheaf.IsSheaf
      ((((TopCat.of ℕ).presheafToTypes A) ⋙ TopCat.discrete) ⋙ forget TopCat) := by
  -- Forgetting the discrete topology recovers the underlying dependent-function presheaf of sets.
  simpa using (TopCat.Presheaf.toTypes_isSheaf (X := TopCat.of ℕ) A)

/-- Helper for Example 6.9.4: every singleton section space is nontrivial as soon as the
corresponding fibre is nontrivial. -/
lemma singleton_section_nontrivial (hA : ∀ n : ℕ, Nontrivial (A n)) (n : ℕ) :
    Nontrivial (((TopCat.of ℕ).presheafToTypes A).obj (Opposite.op (singleton_cover n))) := by
  classical
  -- A section over `{n}` is determined by its value at the unique point of the singleton.
  change Nontrivial (∀ x : singleton_cover n, A x.1)
  let x₀ : singleton_cover n := ⟨n, Set.mem_singleton n⟩
  let _ := hA n
  obtain ⟨a, b, hab⟩ := exists_pair_ne (A n)
  let f : ∀ x : singleton_cover n, A x.1 :=
    fun x => Eq.ndrec a (Set.mem_singleton_iff.mp x.2).symm
  let g : ∀ x : singleton_cover n, A x.1 :=
    fun x => Eq.ndrec b (Set.mem_singleton_iff.mp x.2).symm
  refine ⟨⟨f, g, ?_⟩⟩
  intro hfg
  have hfg₀ : f x₀ = g x₀ := congrFun hfg x₀
  have hab' : a = b := by
    simpa [f, g, x₀] using hfg₀
  exact hab hab'

/-- Helper for Example 6.9.4: the singleton-cover factors remain nontrivial after adding the
discrete topology to each section space. -/
lemma singleton_cover_factor_nontrivial (hA : ∀ n : ℕ, Nontrivial (A n)) (n : ℕ) :
    Nontrivial ((sectionwise_discrete_presheaf A).obj (Opposite.op (singleton_cover n))) := by
  -- The discrete functor changes only the topology, not the underlying singleton-section type.
  change Nontrivial (((TopCat.of ℕ).presheafToTypes A).obj (Opposite.op (singleton_cover n)))
  exact singleton_section_nontrivial (A := A) hA n

/-- Helper for Example 6.9.4: an infinite product of nontrivial discrete factors indexed by `ℕ`
is not discrete in the product topology. -/
lemma pi_not_discrete_of_nontrivial {B : ℕ → Type v} [∀ n : ℕ, TopologicalSpace (B n)]
    (hB : ∀ n : ℕ, Nontrivial (B n)) :
    ¬ DiscreteTopology (∀ n : ℕ, B n) := by
  classical
  intro hdisc
  let x : ∀ n : ℕ, B n := fun n =>
    let _ := hB n
    Classical.choose (exists_pair_ne (B n))
  let y : ∀ n : ℕ, B n := fun n =>
    let _ := hB n
    Classical.choose (exists_ne (x n))
  have hyx : ∀ n : ℕ, y n ≠ x n := by
    intro n
    let _ := hB n
    exact Classical.choose_spec (exists_ne (x n))
  have hsingleton : ({x} : Set (∀ n : ℕ, B n)) ∈ nhds x := by
    -- Discreteness would force the singleton `{x}` to be open, hence a neighborhood of `x`.
    have hopen : IsOpen ({x} : Set (∀ n : ℕ, B n)) :=
      discreteTopology_iff_isOpen_singleton.mp hdisc x
    exact hopen.mem_nhds (by simp)
  rcases exists_finset_piecewise_mem_of_mem_nhds hsingleton y with ⟨I, hI⟩
  let n : ℕ := I.sup id + 1
  have hnI : n ∉ I := by
    intro hn
    have hle : id n ≤ I.sup id := Finset.le_sup hn
    exact Nat.not_succ_le_self (I.sup id) (by simpa [n] using hle)
  have hpiecewise : I.piecewise x y = x := by
    simpa using hI
  have hyxn : y n = x n := by
    simpa [Finset.piecewise, hnI, n] using congrFun hpiecewise n
  exact hyx n hyxn

/-- Helper for Example 6.9.4: for the singleton cover of the discrete base `ℕ`, the two maps in
the equalizer-products sheaf diagram agree for the sectionwise-discrete presheaf. -/
lemma singleton_cover_leftRes_eq_rightRes :
    TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
        (sectionwise_discrete_presheaf A) singleton_cover
      =
    TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
        (sectionwise_discrete_presheaf A) singleton_cover := by
  -- On the diagonal the two restriction maps are the same, and off the diagonal the target is
  -- the empty intersection, so there are no points to distinguish the two maps.
  apply TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.hom_ext
  intro p
  rcases p with ⟨i, j⟩
  by_cases h : i = j
  · subst h
    -- The diagonal branch compares the same restriction map from `{i}` to `{i} ∩ {i}`.
    dsimp [TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes,
      TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes]
    have hleft :
        (Pi.lift fun p ↦
            Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) p.1 ≫
              TopCat.discrete.map
                (((TopCat.of ℕ).presheafToTypes A).map
                  ((singleton_cover p.1).infLELeft (singleton_cover p.2)).op)) ≫
          limit.π
            (Discrete.functor
              fun p ↦ TopCat.discrete.obj ((x : ↥(singleton_cover p.1 ⊓ singleton_cover p.2)) → A ↑x))
            { as := (i, i) } =
          Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) i ≫
            TopCat.discrete.map
              (((TopCat.of ℕ).presheafToTypes A).map
                ((singleton_cover i).infLELeft (singleton_cover i)).op) := by
      simpa using
        (Pi.lift_π
          (p := fun p ↦
            Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) p.1 ≫
              TopCat.discrete.map
                (((TopCat.of ℕ).presheafToTypes A).map
                  ((singleton_cover p.1).infLELeft (singleton_cover p.2)).op))
          (i, i))
    have hright :
        (Pi.lift fun p ↦
            Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) p.2 ≫
              TopCat.discrete.map
                (((TopCat.of ℕ).presheafToTypes A).map
                  ((singleton_cover p.1).infLERight (singleton_cover p.2)).op)) ≫
          limit.π
            (Discrete.functor
              fun p ↦ TopCat.discrete.obj ((x : ↥(singleton_cover p.1 ⊓ singleton_cover p.2)) → A ↑x))
            { as := (i, i) } =
          Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) i ≫
            TopCat.discrete.map
              (((TopCat.of ℕ).presheafToTypes A).map
                ((singleton_cover i).infLERight (singleton_cover i)).op) := by
      simpa using
        (Pi.lift_π
          (p := fun p ↦
            Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) p.2 ≫
              TopCat.discrete.map
                (((TopCat.of ℕ).presheafToTypes A).map
                  ((singleton_cover p.1).infLERight (singleton_cover p.2)).op))
          (i, i))
    have hle : ((singleton_cover i).infLELeft (singleton_cover i)).op =
        ((singleton_cover i).infLERight (singleton_cover i)).op := by
      simpa using congrArg Quiver.Hom.op
        (Subsingleton.elim
          ((singleton_cover i).infLELeft (singleton_cover i))
          ((singleton_cover i).infLERight (singleton_cover i)))
    have hleft' :
        (Pi.lift fun p ↦
            Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) p.1 ≫
              TopCat.discrete.map
                (((TopCat.of ℕ).presheafToTypes A).map
                  ((singleton_cover p.1).infLELeft (singleton_cover p.2)).op)) ≫
          limit.π
            (Discrete.functor
              fun p ↦ TopCat.discrete.obj ((x : ↥(singleton_cover p.1 ⊓ singleton_cover p.2)) → A ↑x))
            { as := (i, i) } =
          Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) i ≫
            TopCat.discrete.map
              (((TopCat.of ℕ).presheafToTypes A).map
                ((singleton_cover i).infLELeft (singleton_cover i)).op) := by
      simpa [singleton_cover] using hleft
    have hright' :
        Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) i ≫
            TopCat.discrete.map
              (((TopCat.of ℕ).presheafToTypes A).map
                ((singleton_cover i).infLERight (singleton_cover i)).op) =
          (Pi.lift fun p ↦
              Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) p.2 ≫
                TopCat.discrete.map
                  (((TopCat.of ℕ).presheafToTypes A).map
                    ((singleton_cover p.1).infLERight (singleton_cover p.2)).op)) ≫
            limit.π
              (Discrete.functor
                fun p ↦
                  TopCat.discrete.obj ((x : ↥(singleton_cover p.1 ⊓ singleton_cover p.2)) → A ↑x))
              { as := (i, i) } := by
      simpa [singleton_cover] using hright.symm
    have hmid :
        Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) i ≫
            TopCat.discrete.map
              (((TopCat.of ℕ).presheafToTypes A).map
                ((singleton_cover i).infLELeft (singleton_cover i)).op) =
          Pi.π (fun i ↦ TopCat.discrete.obj ((x : ↥(singleton_cover i)) → A ↑x)) i ≫
            TopCat.discrete.map
              (((TopCat.of ℕ).presheafToTypes A).map
                ((singleton_cover i).infLERight (singleton_cover i)).op) := by
      rw [hle]
    exact hleft'.trans (hmid.trans hright')
  · -- Off the diagonal the intersection is empty, so the codomain section space is subsingleton.
    have hij : singleton_cover i ⊓ singleton_cover j = ⊥ := by
      ext n
      constructor
      · intro hn
        simp only [singleton_cover, SetLike.mem_coe] at hn
        exact (h (hn.1.symm.trans hn.2)).elim
      · intro hn
        exact False.elim (by simpa using hn)
    ext x
    have hsub :
        Subsingleton ((sectionwise_discrete_presheaf A).obj
          (Opposite.op (singleton_cover i ⊓ singleton_cover j))) := by
      change Subsingleton ((y : ↥(singleton_cover i ⊓ singleton_cover j)) → A ↑y)
      have hempty : IsEmpty ↥(singleton_cover i ⊓ singleton_cover j) := by
        refine ⟨fun y ↦ ?_⟩
        have hy :
            y.1 ∈
              (singleton_cover i ⊓ singleton_cover j :
                TopologicalSpace.Opens (TopCat.of ℕ)) := y.2
        simpa [hij] using hy
      let _ := hempty
      infer_instance
    exact hsub.elim _ _

/-- Helper for Example 6.9.4: if the sectionwise-discrete presheaf were a sheaf, then the
singleton-cover restriction map would have to be an isomorphism. -/
lemma singleton_cover_res_isIso
    (hF : TopCat.Presheaf.IsSheaf (sectionwise_discrete_presheaf A)) :
    IsIso
      (TopCat.Presheaf.SheafConditionEqualizerProducts.res
        (sectionwise_discrete_presheaf A) singleton_cover) := by
  -- The singleton cover turns the sheaf fork into an equalizer of two identical arrows.
  let hEq :=
    (TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts (sectionwise_discrete_presheaf A)).mp hF
  rcases hEq singleton_cover with ⟨hlimit⟩
  simpa using
    CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_eq
      (singleton_cover_leftRes_eq_rightRes (A := A)) hlimit

/-- Example 6.9.4 (3): if each fibre `A i` has at least two elements, then equipping
`U ↦ ∏ i : U, A i` with the discrete topology on each section space does not produce a sheaf of
topological spaces, even though the underlying presheaf of sets is a sheaf. -/
-- Proof sketch: combine the sheaf obstruction for the sectionwise-discrete topology with the
-- nontriviality hypothesis on each fibre.
theorem presheafToTypes_discrete_not_isSheaf (hA : ∀ i : ℕ, Nontrivial (A i)) :
    ¬ TopCat.Presheaf.IsSheaf (((TopCat.of ℕ).presheafToTypes A) ⋙ TopCat.discrete) := by
  intro hF
  -- The sheaf condition would make the singleton-cover restriction map an isomorphism.
  let _ := singleton_cover_res_isIso (A := A) hF
  let e :
      (sectionwise_discrete_presheaf A).obj (Opposite.op (iSup singleton_cover)) ≃ₜ
        TopCat.of
          (∀ n : ℕ, (sectionwise_discrete_presheaf A).obj (Opposite.op (singleton_cover n))) :=
    TopCat.homeoOfIso
      ((asIso
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res
            (sectionwise_discrete_presheaf A) singleton_cover)) ≪≫
        TopCat.piIsoPi
          (fun n : ℕ => (sectionwise_discrete_presheaf A).obj (Opposite.op (singleton_cover n))))
  have hsource :
      DiscreteTopology ((sectionwise_discrete_presheaf A).obj (Opposite.op (iSup singleton_cover))) := by
    -- Every value of the presheaf is discrete by construction.
    simpa [sectionwise_discrete_presheaf] using
      (inferInstance :
        DiscreteTopology
          (TopCat.discrete.obj
            (((TopCat.of ℕ).presheafToTypes A).obj (Opposite.op (iSup singleton_cover)))))
  have htarget :
      DiscreteTopology
        (∀ n : ℕ, (sectionwise_discrete_presheaf A).obj (Opposite.op (singleton_cover n))) := by
    -- A homeomorphism transports the discrete topology from the source to the product object.
    let _ := hsource
    simpa using e.discreteTopology
  -- This contradicts the fact that an infinite product of nontrivial discrete factors is not discrete.
  exact
    (pi_not_discrete_of_nontrivial
      (B := fun n : ℕ => (sectionwise_discrete_presheaf A).obj (Opposite.op (singleton_cover n)))
      (fun n => singleton_cover_factor_nontrivial (A := A) hA n))
      htarget

end
