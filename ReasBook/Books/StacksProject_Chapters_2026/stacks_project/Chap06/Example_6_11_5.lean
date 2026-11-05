module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.Sheaves.SheafOfFunctions


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace Filter TopCat
open CategoryTheory.Limits
open scoped Topology

universe u

noncomputable section

/-
Domain-style sampling for Example 6.11.5:
- primary domain: sheaves of set-valued functions on a topological space, their stalks, and stalk
  evaluation maps;
- sampled owner API:
  `TopCat.presheafToTypes`,
  `TopCat.sheafToTypes`,
  `TopCat.presheafToType`,
  `TopCat.stalkToFiber`;
- owner abstraction:
  the core/canonical owners are the sheaves of all functions `TopCat.sheafToTypes` /
  `TopCat.sheafToType`, with `TopCat.stalkToFiber` giving the canonical evaluation pattern for
  local-predicate subsheaves;
- primitive-vs-derived split:
  primitive data are the family `A : X → Type u`, the point `x : X`, and later the sequence
  `sequence : ℕ → X`;
  the source-facing evaluation map on stalks is defined directly on the owner
  `TopCat.sheafToTypes`, following the same colimit-level evaluation pattern as
  `TopCat.stalkToFiber`, while the binary-tail map is derived from a cocone into
  `Filter.Germ atTop Bool`;
- source/core/bridge triage:
  `source-facing`: `dependentFunctionStalkToFiber` and `stalkToBinaryTail`;
  `core/canonical`: `TopCat.sheafToTypes`, `TopCat.sheafToType`, `TopCat.stalkToFiber`,
    `TopCat.stalkToFiber_germ`;
  `bridge/view`: the neighborhood cocone encoding eventual tails.
-/

section

variable {X : TopCat.{u}} (A : X → Type u) (x : X)

/-- Example 6.11.5 (1): for the sheaf `U ↦ ∏_{y ∈ U} A_y` on a topological space `X`, there is a
canonical evaluation map from the stalk at `x` to the fiber `A_x`. This is the direct
all-functions analogue of mathlib's canonical `TopCat.stalkToFiber`. -/
noncomputable def dependentFunctionStalkToFiber :
    (X.sheafToTypes A).presheaf.stalk x ⟶ A x :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf)
    { pt := A x
      ι :=
        { app := fun U f ↦ f ⟨x, (unop U).2⟩
          naturality := by
            intro U V i
            funext f
            rfl } }

-- Proof sketch: this is the defining evaluation formula for the colimit cocone used in
-- `dependentFunctionStalkToFiber`.
/-- The canonical map from the stalk to the fiber sends a germ to the value of the section at `x`.
-/
theorem dependentFunctionStalkToFiber_germ (U : Opens X) (hx : x ∈ U)
    (f : (X.sheafToTypes A).presheaf.obj (op U)) :
    dependentFunctionStalkToFiber A x ((X.sheafToTypes A).presheaf.germ U x hx f) = f ⟨x, hx⟩ := by
  simp [Presheaf.germ, dependentFunctionStalkToFiber]

-- Proof sketch: if a stalk element were represented by a germ over some neighborhood `U`, then the
-- assumed point `y ∈ U` with empty fiber would force that section set to be empty, so no germ can
-- exist and the colimit defining the stalk is empty.
/-- If every neighborhood of `x` contains a point with empty fiber, then the stalk at `x` is empty.
-/
theorem isEmpty_stalk_of_exists_empty_fiber_in_every_openNhds
    (h : ∀ U : OpenNhds x, ∃ y : U.1, IsEmpty (A y)) :
    IsEmpty ((X.sheafToTypes A).presheaf.stalk x) := by
  refine ⟨fun t ↦ ?_⟩
  obtain ⟨U, hxU, f, rfl⟩ := (X.sheafToTypes A).presheaf.germ_exist x t
  obtain ⟨y, hy⟩ := h ⟨U, hxU⟩
  exact hy.false (f y)

end

namespace Example_6_11_5

open Filter.Germ

section

variable {X : TopCat.{u}} {x : X} {sequence : ℕ → X}

public abbrev binaryNeighborhoodPresheaf (x : X) :=
  (OpenNhds.inclusion x).op ⋙ (X.sheafToType (ULift.{u} Bool)).presheaf

private theorem eventually_mem (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x)) (U : OpenNhds x) :
    ∀ᶠ n : ℕ in atTop, sequence n ∈ U.1 := by
  exact hsequence (U.1.2.mem_nhds U.2)

/-- The leg of the cocone sending a neighborhood section around `x` to its eventual binary tail
along a sequence converging to `x`. -/
public def stalkToBinaryTailLeg (x : X) (sequence : ℕ → X) (U : (OpenNhds x)ᵒᵖ) :
    (binaryNeighborhoodPresheaf x).obj U ⟶
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool) := by
  classical
  intro f
  exact
    ((fun n : ℕ ↦
        if h : sequence n ∈ (unop U).1 then
          f ⟨sequence n, h⟩
        else
          ULift.up false) :
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool))

private theorem restrict_apply (x : X) (sequence : ℕ → X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V)
    (f : (binaryNeighborhoodPresheaf x).obj U)
    (n : ℕ) (hn : sequence n ∈ (unop V).1) :
    ((binaryNeighborhoodPresheaf x).map i f) ⟨sequence n, hn⟩ =
      f ⟨sequence n, i.unop.le hn⟩ := rfl

public theorem stalkToBinaryTailLeg_naturality (x : X) (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x))
    {U V : (OpenNhds x)ᵒᵖ}
    (i : U ⟶ V) :
    ((binaryNeighborhoodPresheaf x).map i) ≫ stalkToBinaryTailLeg x sequence V =
      stalkToBinaryTailLeg x sequence U := by
  classical
  funext f
  change
    ((fun n : ℕ ↦
        if h : sequence n ∈ (unop V).1 then
          ((binaryNeighborhoodPresheaf x).map i f) ⟨sequence n, h⟩
        else
          ULift.up false) :
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) =
      ((fun n : ℕ ↦
          if h : sequence n ∈ (unop U).1 then
            f ⟨sequence n, h⟩
          else
            ULift.up false) :
        Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool))
  apply coe_eq.2
  filter_upwards [eventually_mem sequence hsequence (unop V)] with n hn
  have hU : sequence n ∈ (unop U).1 := i.unop.le hn
  simp only [hn, hU]
  exact restrict_apply x sequence i f n hn

/-- The cocone realizing the map from the stalk at `x` to tails of binary sequences along
`sequence`. -/
public def stalkToBinaryTailCocone (x : X) (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x)) :
    Cocone (binaryNeighborhoodPresheaf x) where
  pt := Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)
  ι :=
    { app := fun U ↦ stalkToBinaryTailLeg x sequence U
      naturality := fun _ _ i ↦
        stalkToBinaryTailLeg_naturality x sequence hsequence i }

-- Proof sketch: a section on a neighborhood of `∞` determines a binary sequence on all large
-- integers, hence a germ at `atTop`; the cocone above packages this eventual-equality class.
/-- A convergent sequence `sequence n → x` induces a canonical map from the stalk at `x` of the
sheaf of `{0,1}`-valued functions to the set of tails of binary sequences, encoded as germs in
`Filter.Germ atTop (ULift Bool)`. -/
noncomputable def stalkToBinaryTail (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x)) :
    (X.sheafToType (ULift.{u} Bool)).presheaf.stalk x ⟶
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool) :=
  colimit.desc _ (stalkToBinaryTailCocone x sequence hsequence)

private def binarySectionOfSequence (sequence : ℕ → X) (b : ℕ → ULift.{u} Bool) :
    (X.sheafToType (ULift.{u} Bool)).presheaf.obj (op (⊤ : Opens X)) := by
  classical
  intro y
  exact
    if hy : y.1 ∈ Set.range sequence then
      b (Function.invFun sequence y.1)
    else
      ULift.up false

private theorem binarySectionOfSequence_apply (sequence : ℕ → X)
    (hsequence_injective : Function.Injective sequence)
    (b : ℕ → ULift.{u} Bool) (n : ℕ) :
    binarySectionOfSequence sequence b ⟨sequence n, by trivial⟩ = b n := by
  classical
  rw [binarySectionOfSequence]
  have hleft := Function.leftInverse_invFun hsequence_injective n
  simp [hleft]

/-- The stalk element determined by the global section attached to a binary sequence, with value
`false` away from the range of `sequence`. -/
private def stalkOfBinarySequence (x : X) (sequence : ℕ → X) (b : ℕ → ULift.{u} Bool) :
    (X.sheafToType (ULift.{u} Bool)).presheaf.stalk x :=
  (X.sheafToType (ULift.{u} Bool)).presheaf.germ (⊤ : Opens X) x (by trivial)
    (binarySectionOfSequence sequence b)

private theorem stalkToBinaryTailLeg_top (hsequence_injective : Function.Injective sequence)
    (b : ℕ → ULift.{u} Bool) :
    stalkToBinaryTailLeg x sequence (op ⟨(⊤ : Opens X), by trivial⟩)
        (binarySectionOfSequence sequence b) =
      (b : Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
  classical
  apply coe_eq.2
  exact Filter.Eventually.of_forall fun n ↦ by
    have htop : sequence n ∈ (⊤ : Opens X) := by trivial
    simp [htop, binarySectionOfSequence_apply sequence hsequence_injective b n]

-- Proof sketch: for the global section attached to a binary sequence `b`, the induced tail germ is
-- exactly `b` itself, because the top open contains every term of the sequence.
/-- The stalk-to-tail map sends the germ of the global section attached to a binary sequence `b`
to the tail class of `b`. -/
private theorem stalkToBinaryTail_stalkOfBinarySequence
    (hsequence : Tendsto sequence atTop (nhds x))
    (hsequence_injective : Function.Injective sequence) (b : ℕ → ULift.{u} Bool) :
    stalkToBinaryTail sequence hsequence (stalkOfBinarySequence x sequence b) =
      (b : Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
  classical
  rw [stalkOfBinarySequence, TopCat.Presheaf.germ, stalkToBinaryTail]
  simpa only [Types.Colimit.ι_desc_apply, stalkToBinaryTailCocone] using
    stalkToBinaryTailLeg_top hsequence_injective b

-- Proof sketch: every germ of a binary sequence is represented by an actual sequence `b : ℕ →
-- Bool`, and injectivity of `sequence` lets us realize it by a global `{0,1}`-valued function on
-- `X` whose restriction to the sequence is exactly `b`.
/-- Example 6.11.5 (2): if `sequence n → x` and the points `sequence n` are pairwise distinct, then
the stalk of the `{0,1}`-valued function sheaf at `x` surjects onto the set of tails of binary
sequences. -/
theorem stalkToBinaryTail_surjective (hsequence : Tendsto sequence atTop (nhds x))
    (hsequence_injective : Function.Injective sequence) :
    Function.Surjective (stalkToBinaryTail sequence hsequence) := by
  intro g
  refine inductionOn g ?_
  intro b
  exact ⟨stalkOfBinarySequence x sequence b,
    stalkToBinaryTail_stalkOfBinarySequence hsequence hsequence_injective b⟩

private theorem constFalseTail_ne_modifiedAlternatingTail (n₀ : ℕ) :
    ((fun _ : ℕ ↦ ULift.up false) :
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) ≠
      ((fun n : ℕ ↦ if n = n₀ then ULift.up false else ULift.up (decide (n % 2 = 0))) :
        Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
  intro h
  have h' := coe_eq.mp h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h'
  let m := 2 * max N (n₀ + 1)
  have hmN : N ≤ m := by
    dsimp [m]
    omega
  have hmn₀ : m ≠ n₀ := by
    dsimp [m]
    omega
  have hmEven : m % 2 = 0 := by
    dsimp [m]
    omega
  have hm := hN m hmN
  simp [m, hmn₀, hmEven] at hm

private theorem stalkToFiber_stalkOfBinarySequence_of_mem
    (b : ℕ → ULift.{u} Bool) (hx : x ∈ Set.range sequence) :
    dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
        (stalkOfBinarySequence x sequence b) =
      b (Function.invFun sequence x) := by
  classical
  simpa [stalkOfBinarySequence, binarySectionOfSequence, hx] using
    dependentFunctionStalkToFiber_germ (fun _ : X ↦ ULift.{u} Bool) x (⊤ : Opens X) (by trivial)
      (binarySectionOfSequence sequence b)

private theorem stalkToFiber_stalkOfBinarySequence_of_not_mem
    (b : ℕ → ULift.{u} Bool) (hx : x ∉ Set.range sequence) :
    dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
        (stalkOfBinarySequence x sequence b) =
      ULift.up false := by
  classical
  simpa [stalkOfBinarySequence, binarySectionOfSequence, hx] using
    dependentFunctionStalkToFiber_germ (fun _ : X ↦ ULift.{u} Bool) x (⊤ : Opens X) (by trivial)
      (binarySectionOfSequence sequence b)

-- Proof sketch: the constant-zero sequence and the parity sequence define two distinct stalk
-- elements because their tails are not eventually equal, but both evaluate to `false` at `∞`.
/-- Example 6.11.5 (3): if `sequence n → x` and the points `sequence n` are pairwise distinct, then
the canonical map from the stalk at `x` of the sheaf of `{0,1}`-valued functions to the fiber
`{0,1}` is not injective. -/
theorem binaryStalkToFiber_not_injective (hsequence : Tendsto sequence atTop (nhds x))
    (hsequence_injective : Function.Injective sequence) :
    ¬ Function.Injective (dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x) := by
  classical
  intro hInj
  let n₀ := Function.invFun sequence x
  let b₁ : ℕ → ULift.{u} Bool := fun n ↦
    if n = n₀ then ULift.up false else ULift.up (decide (n % 2 = 0))
  have hFiber :
      dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
          (stalkOfBinarySequence x sequence (fun _ : ℕ ↦ ULift.up false)) =
        dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
          (stalkOfBinarySequence x sequence b₁) := by
    by_cases hx : x ∈ Set.range sequence
    · rw [stalkToFiber_stalkOfBinarySequence_of_mem _ hx,
        stalkToFiber_stalkOfBinarySequence_of_mem _ hx]
      simp [b₁, n₀]
    · rw [stalkToFiber_stalkOfBinarySequence_of_not_mem _ hx,
        stalkToFiber_stalkOfBinarySequence_of_not_mem _ hx]
  have hStalk :
      stalkOfBinarySequence x sequence (fun _ : ℕ ↦ ULift.up false) =
        stalkOfBinarySequence x sequence b₁ := by
    exact hInj hFiber
  have hTail :
      ((fun _ : ℕ ↦ ULift.up false) :
        Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) =
        (b₁ : Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
    have hTailMap := congrArg (stalkToBinaryTail sequence hsequence) hStalk
    exact
      (stalkToBinaryTail_stalkOfBinarySequence hsequence
          hsequence_injective (fun _ : ℕ ↦ ULift.up false)).symm.trans <|
        hTailMap.trans <|
          stalkToBinaryTail_stalkOfBinarySequence hsequence hsequence_injective b₁
  exact constFalseTail_ne_modifiedAlternatingTail n₀ hTail

end

end Example_6_11_5
