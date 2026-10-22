/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part12

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- Definition 26.0.1: a multivalued mapping `ρ` is single-valued if for every `x`, the value
`ρ x` contains at most one point. -/
def IsSingleValuedMultivaluedMap {X Y : Type*} (ρ : X → Set Y) : Prop :=
  ∀ x, Set.Subsingleton (ρ x)

/-- Definition 26.0.2: the inverse multivalued mapping of `ρ` sends `x*` to the set of all
`x` such that `x* ∈ ρ(x)`. -/
def inverseMultivaluedMap {X Y : Type*} (ρ : X → Set Y) : Y → Set X :=
  fun xStar => {x | xStar ∈ ρ x}

/-- Definition 26.0.3: a multivalued mapping `ρ` is one-to-one precisely when both `ρ` and its
inverse multivalued mapping `ρ⁻¹` are single-valued. -/
def IsOneToOneMultivaluedMap {X Y : Type*} (ρ : X → Set Y) : Prop :=
  IsSingleValuedMultivaluedMap ρ ∧
    IsSingleValuedMultivaluedMap (inverseMultivaluedMap ρ)

/-- The graph of a multivalued mapping `ρ` consists of the pairs `(x, y)` with `y ∈ ρ x`. -/
def multivaluedMapGraph {X Y : Type*} (ρ : X → Set Y) : Set (X × Y) :=
  {p | p.2 ∈ ρ p.1}

/-- Helper for Lemma 26.1: membership in the graph of `ρ` is exactly membership in the fiber
`ρ x`. -/
lemma helperForLemma_26_1_graphMembership_iff {X Y : Type*} (ρ : X → Set Y) (x : X) (y : Y) :
    (x, y) ∈ multivaluedMapGraph ρ ↔ y ∈ ρ x := by
  -- This is just the definition of the graph unpacked at the pair `(x, y)`.
  rfl

/-- Helper for Lemma 26.1: single-valuedness of `ρ` is equivalent to uniqueness of the second
coordinate inside each graph fiber over a fixed `x`. -/
lemma helperForLemma_26_1_graphFiberUniqueness_iff_singleValued {X Y : Type*} (ρ : X → Set Y) :
    IsSingleValuedMultivaluedMap ρ ↔
      ∀ ⦃x y₁ y₂⦄,
        (x, y₁) ∈ multivaluedMapGraph ρ →
          (x, y₂) ∈ multivaluedMapGraph ρ →
            y₁ = y₂ := by
  constructor
  · intro hSingle x y₁ y₂ hy₁ hy₂
    -- Move from graph membership back to the fiber `ρ x` and use subsingletonness there.
    exact hSingle x
      ((helperForLemma_26_1_graphMembership_iff ρ x y₁).1 hy₁)
      ((helperForLemma_26_1_graphMembership_iff ρ x y₂).1 hy₂)
  · intro hUnique x y₁ hy₁ y₂ hy₂
    -- Repackage two fiber members as graph points with the same first coordinate.
    exact hUnique
      ((helperForLemma_26_1_graphMembership_iff ρ x y₁).2 hy₁)
      ((helperForLemma_26_1_graphMembership_iff ρ x y₂).2 hy₂)

/-- Helper for Lemma 26.1: single-valuedness of `ρ⁻¹` is equivalent to uniqueness of the first
coordinate inside each graph fiber over a fixed `x*`. -/
lemma helperForLemma_26_1_swappedGraphFiberUniqueness_iff_inverseSingleValued
    {X Y : Type*} (ρ : X → Set Y) :
    IsSingleValuedMultivaluedMap (inverseMultivaluedMap ρ) ↔
      ∀ ⦃x₁ x₂ y⦄,
        (x₁, y) ∈ multivaluedMapGraph ρ →
          (x₂, y) ∈ multivaluedMapGraph ρ →
            x₁ = x₂ := by
  constructor
  · intro hSingle x₁ x₂ y hx₁ hx₂
    -- Rewrite both graph points as members of the inverse fiber over `y`.
    exact hSingle y
      (by simpa [inverseMultivaluedMap] using hx₁)
      (by simpa [inverseMultivaluedMap] using hx₂)
  · intro hUnique y x₁ hx₁ x₂ hx₂
    -- Turn inverse-fiber membership back into graph membership with common second coordinate.
    exact hUnique
      (by simpa [inverseMultivaluedMap] using hx₁)
      (by simpa [inverseMultivaluedMap] using hx₂)

-- Proof sketch: unfold the definitions of one-to-one and graph, then rewrite single-valuedness
-- of `ρ` and `ρ⁻¹` as uniqueness of the second and first coordinates among graph points.
/-- Lemma 26.1: a multivalued mapping `ρ` is one-to-one exactly when its graph contains neither
two distinct pairs with the same first coordinate nor two distinct pairs with the same second
coordinate. -/
theorem isOneToOneMultivaluedMap_iff_graph_coordinate_uniqueness {X Y : Type*} (ρ : X → Set Y) :
    IsOneToOneMultivaluedMap ρ ↔
      ((∀ ⦃x y₁ y₂⦄,
          (x, y₁) ∈ multivaluedMapGraph ρ →
            (x, y₂) ∈ multivaluedMapGraph ρ →
              y₁ = y₂) ∧
        ∀ ⦃x₁ x₂ y⦄,
          (x₁, y) ∈ multivaluedMapGraph ρ →
            (x₂, y) ∈ multivaluedMapGraph ρ →
              x₁ = x₂) := by
  -- Split one-to-one into the single-valuedness of `ρ` and of `ρ⁻¹`.
  constructor
  · intro hOneToOne
    constructor
    · -- The first half says that a fixed first coordinate determines the second one uniquely.
      exact (helperForLemma_26_1_graphFiberUniqueness_iff_singleValued ρ).1 hOneToOne.1
    · -- The second half says that a fixed second coordinate determines the first one uniquely.
      exact
        (helperForLemma_26_1_swappedGraphFiberUniqueness_iff_inverseSingleValued ρ).1
          hOneToOne.2
  · intro hGraph
    constructor
    · -- Rebuild single-valuedness of `ρ` from uniqueness in each graph fiber over `x`.
      exact (helperForLemma_26_1_graphFiberUniqueness_iff_singleValued ρ).2 hGraph.1
    · -- Rebuild single-valuedness of `ρ⁻¹` from uniqueness in each graph fiber over `x*`.
      exact
        (helperForLemma_26_1_swappedGraphFiberUniqueness_iff_inverseSingleValued ρ).2
          hGraph.2

/-- The convex-analytic condition that the subdifferential of `f` is single-valued on its
effective domain and injective there. -/
def HasSingleValuedInjectiveSubdifferential {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunction f ∧
    (∀ x ∈ subdifferentialEffectiveDomain f, Set.Subsingleton (subdifferentialAt f x)) ∧
      ∀ ⦃x y g⦄,
        x ∈ subdifferentialEffectiveDomain f →
          y ∈ subdifferentialEffectiveDomain f →
            g ∈ subdifferentialAt f x →
              g ∈ subdifferentialAt f y →
                x = y

/-- The gradient image of `C` under `f`, which is the dual domain used in the Legendre
conjugate construction. -/
def legendreGradientImage {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  gradient f '' C

-- Proof sketch: unfold the image set and use the original point `x` as the witness.
/-- Every gradient value of a point of `C` lies in the gradient image of `C`. -/
lemma mem_legendreGradientImage {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) :
    gradient f x ∈ legendreGradientImage C f := by
  -- Unfold the image definition and use the original source point as the witness.
  exact ⟨x, hx, rfl⟩

/-- Definition 26.4.0.1: the Legendre conjugate of a differentiable real-valued function `f` on
an open set `C ⊆ ℝ^n` is the pair `(D, g)` where `D` is the image of `C` under the gradient map
`∇ f`, and `g` is the real-valued function on `D` given by
`g (xStar) = ⟪(∇ f)⁻¹ xStar, xStar⟫ - f ((∇ f)⁻¹ xStar)`. The field
`fiber_well_defined` records the weaker hypothesis from the text ensuring that this formula is
independent of the chosen preimage in a gradient fiber, so injectivity of `∇ f` is not assumed
in the definition. -/
structure LegendreConjugateOn {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) where
  isOpen_source : IsOpen C
  differentiableOn_source : DifferentiableOn ℝ f C
  conjFun : legendreGradientImage C f → ℝ
  fiber_well_defined : ∀ ⦃x₁ x₂ xStar : EuclideanSpace ℝ (Fin n)⦄,
      x₁ ∈ C →
      x₂ ∈ C →
      gradient f x₁ = xStar →
      gradient f x₂ = xStar →
      dotProduct x₁ xStar - f x₁ = dotProduct x₂ xStar - f x₂
  value_eq : ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, (hx : x ∈ C) →
      conjFun ⟨gradient f x, mem_legendreGradientImage (C := C) (f := f) (x := x) hx⟩ =
        (dotProduct (fun i => x i) (fun i => gradient f x i) - f x)

/-- Auxiliary package recording a Legendre-conjugate construction relative to a chosen pairing
and a chosen map on the source set. -/
structure LegendreConjugatePackageOn {X Y : Type*} (pair : X → Y → ℝ) (C : Set X) (f : X → EReal) where
  target : Set Y
  conjFun : Y → EReal
  toFun : X → Y
  image_eq : target = toFun '' C
  fiber_well_defined : ∀ ⦃x₁ x₂ xStar⦄,
      x₁ ∈ C →
      x₂ ∈ C →
      toFun x₁ = xStar →
      toFun x₂ = xStar →
      (((pair x₁ xStar : ℝ) : EReal) - f x₁) =
        (((pair x₂ xStar : ℝ) : EReal) - f x₂)
  value_eq : ∀ ⦃x⦄, x ∈ C → conjFun (toFun x) = (((pair x (toFun x) : ℝ) : EReal) - f x)

/-- Definition 26.4.0.2: passing from `(C, f)` to its well-defined Legendre conjugate `(D, g)`
is called the Legendre transformation. In the Euclidean differentiable setting fixed in
Definition 26.4.0.1, this is exactly the same data as a `LegendreConjugateOn C f`. -/
abbrev LegendreTransformationOn {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :=
  LegendreConjugateOn C f

/-- The chosen gradient on `int (dom f)` for an `EReal`-valued function that is differentiable at
every interior effective-domain point, extended by `0` outside that interior. -/
noncomputable def interiorGradientMap {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x =>
    if hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) then
      erealGradientAt (hdiff x hx)
    else
      0

/-- Helper for Text 26.4.0.2: on the singleton space `Fin 0 → ℝ`, properness forces the
effective domain on `univ` to be all of space. -/
lemma helperForText_26_4_0_2_effectiveDomain_univ_finZero
    {F : (Fin 0 → ℝ) → EReal} (hF : ProperERealFunction F) :
    effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F = Set.univ := by
  ext x
  constructor
  · intro _hx
    -- Any effective-domain point is, in particular, a point of `univ`.
    simp
  · intro _hx
    rcases hF.2 with ⟨x0, hx0_ne_top⟩
    have hx : x = x0 := Subsingleton.elim x x0
    have hx0_mem : x0 ∈ effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F := by
      -- The witness supplied by properness is finite, so it lies in the effective domain.
      rw [effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.mpr hx0_ne_top⟩
    -- Since `Fin 0 → ℝ` is a singleton, every point agrees with that witness.
    simpa [hx] using hx0_mem

/-- Helper for Text 26.4.0.2: any proper convex extension on `Fin 0 → ℝ` has full interior
effective domain, so it cannot realize `C = ∅`. -/
lemma helperForText_26_4_0_2_interior_effectiveDomain_univ_finZero
    {F : (Fin 0 → ℝ) → EReal} (hF : ProperConvexERealFunction (F := (Fin 0 → ℝ)) F) :
    interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = Set.univ := by
  -- First identify the effective domain with `univ` using the properness component.
  rw [helperForText_26_4_0_2_effectiveDomain_univ_finZero hF.1]
  -- The interior of the whole space is again the whole space.
  simp

/-- Helper for Text 26.4.0.2: on `Fin 0 → ℝ`, the interior effective domain of a proper convex
extension is nonempty. -/
lemma helperForText_26_4_0_2_interior_effectiveDomain_nonempty_finZero
    {F : (Fin 0 → ℝ) → EReal} (hF : ProperConvexERealFunction (F := (Fin 0 → ℝ)) F) :
    (interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F)).Nonempty := by
  -- The singleton space has the zero vector, and the previous helper shows that it lies in the
  -- whole interior effective domain.
  refine ⟨0, ?_⟩
  simpa [helperForText_26_4_0_2_interior_effectiveDomain_univ_finZero hF]

/-- Helper for Text 26.4.0.2: for a fixed proper convex function on `Fin 0 → ℝ`, the interior
effective domain cannot be empty. -/
lemma helperForText_26_4_0_2_interior_effectiveDomain_ne_empty_finZero
    {F : (Fin 0 → ℝ) → EReal} (hF : ProperConvexERealFunction (F := (Fin 0 → ℝ)) F) :
    interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) ≠ (∅ : Set (Fin 0 → ℝ)) := by
  -- The previous nonemptiness lemma gives an explicit point in the interior effective domain.
  intro hInteriorEmpty
  rcases helperForText_26_4_0_2_interior_effectiveDomain_nonempty_finZero hF with ⟨x, hx⟩
  -- Rewriting by the claimed emptiness turns that point into an impossible member of `∅`.
  rw [hInteriorEmpty] at hx
  simp at hx

/-- Helper for Text 26.4.0.2: on `Fin 0 → ℝ`, the conclusion `interior (effectiveDomain F) = ∅`
cannot hold for a proper convex extension. -/
lemma helperForText_26_4_0_2_no_emptyInteriorExtension_finZero :
    ¬ ∃ F : (Fin 0 → ℝ) → EReal,
      ProperConvexERealFunction (F := (Fin 0 → ℝ)) F ∧
      interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = (∅ : Set (Fin 0 → ℝ)) := by
  intro h
  rcases h with ⟨F, hF, hInteriorEmpty⟩
  -- The pointwise nonemptiness helper rules out the claimed empty interior immediately.
  exact (helperForText_26_4_0_2_interior_effectiveDomain_ne_empty_finZero hF) hInteriorEmpty

/-- Helper for Text 26.4.0.2: the gradient image of the empty source set is empty. -/
lemma helperForText_26_4_0_2_legendreGradientImage_empty {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    legendreGradientImage (∅ : Set (EuclideanSpace ℝ (Fin n))) f = ∅ := by
  -- Unfold the image definition and note that there are no source points to contribute.
  simp [legendreGradientImage]

/-- Helper for Text 26.4.0.2: no point lies in the gradient image of the empty source set. -/
lemma helperForText_26_4_0_2_false_of_mem_emptyGradientImage {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {xStar : EuclideanSpace ℝ (Fin n)}
    (hxStar : xStar ∈ legendreGradientImage (∅ : Set (EuclideanSpace ℝ (Fin n))) f) :
    False := by
  -- Rewrite the empty gradient image to `∅`, so membership becomes impossible.
  simpa [helperForText_26_4_0_2_legendreGradientImage_empty (n := n) (f := f)] using hxStar

/-- Helper for Text 26.4.0.2: every function is differentiable on the empty zero-dimensional
source set. -/
lemma helperForText_26_4_0_2_differentiableOn_empty_finZero
    {f : EuclideanSpace ℝ (Fin 0) → ℝ} :
    DifferentiableOn ℝ f (∅ : Set (EuclideanSpace ℝ (Fin 0))) := by
  -- The differentiability condition is vacuous because there are no source points.
  intro x hx
  simp at hx

/-- Helper for Text 26.4.0.2: the conjugate function on the empty gradient image is the unique
function out of that empty target type. -/
def helperForText_26_4_0_2_emptyGradientImageConjFun_finZero
    {f : EuclideanSpace ℝ (Fin 0) → ℝ} :
    legendreGradientImage (∅ : Set (EuclideanSpace ℝ (Fin 0))) f → ℝ :=
  fun xStar =>
    False.elim
      (helperForText_26_4_0_2_false_of_mem_emptyGradientImage (f := f)
        (xStar := xStar.1) xStar.2)

/-- Helper for Text 26.4.0.2: fiber well-definedness is vacuous on the empty zero-dimensional
source set. -/
lemma helperForText_26_4_0_2_emptyFiberWellDefined_finZero
    {f : EuclideanSpace ℝ (Fin 0) → ℝ} :
    ∀ ⦃x₁ x₂ xStar : EuclideanSpace ℝ (Fin 0)⦄,
      x₁ ∈ (∅ : Set (EuclideanSpace ℝ (Fin 0))) →
      x₂ ∈ (∅ : Set (EuclideanSpace ℝ (Fin 0))) →
      gradient f x₁ = xStar →
      gradient f x₂ = xStar →
      dotProduct x₁ xStar - f x₁ = dotProduct x₂ xStar - f x₂ := by
  intro x₁ x₂ xStar hx₁ _hx₂ _hgrad₁ _hgrad₂
  -- Source membership already contradicts emptiness, so there is nothing to prove.
  simp at hx₁

/-- Helper for Text 26.4.0.2: the Legendre value formula is vacuous on the empty
zero-dimensional source set. -/
lemma helperForText_26_4_0_2_emptyValueEq_finZero
    {f : EuclideanSpace ℝ (Fin 0) → ℝ} :
    ∀ ⦃x : EuclideanSpace ℝ (Fin 0)⦄, (hx : x ∈ (∅ : Set (EuclideanSpace ℝ (Fin 0)))) →
      helperForText_26_4_0_2_emptyGradientImageConjFun_finZero (f := f)
        ⟨gradient f x,
          mem_legendreGradientImage (C := (∅ : Set (EuclideanSpace ℝ (Fin 0))))
            (f := f) (x := x) hx⟩ =
        (dotProduct (fun i => x i) (fun i => gradient f x i) - f x) := by
  intro x hx
  simp at hx

/-- Helper for Text 26.4.0.2: in the zero-dimensional empty-source case, there is an explicit
vacuous Legendre-transformation package on the empty source set. -/
def helperForText_26_4_0_2_emptyLegendreTransformationSource_finZero
    {f : EuclideanSpace ℝ (Fin 0) → ℝ} :
    LegendreTransformationOn (∅ : Set (EuclideanSpace ℝ (Fin 0))) f :=
  { isOpen_source := isOpen_empty
    differentiableOn_source := helperForText_26_4_0_2_differentiableOn_empty_finZero (f := f)
    conjFun := helperForText_26_4_0_2_emptyGradientImageConjFun_finZero (f := f)
    fiber_well_defined := helperForText_26_4_0_2_emptyFiberWellDefined_finZero (f := f)
    value_eq := helperForText_26_4_0_2_emptyValueEq_finZero (f := f) }

/-- Helper for Text 26.4.0.2: after simplifying the image of `∅`, the zero-dimensional
Legendre-transformation hypothesis is inhabited. -/
lemma helperForText_26_4_0_2_nonemptyLegendreTransformation_finZero
    {f : EuclideanSpace ℝ (Fin 0) → ℝ} :
    Nonempty
      (LegendreTransformationOn
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
        f) := by
  -- The image of the empty set is empty, so the explicit vacuous package applies directly.
  simpa [Set.image_empty] using
    (show Nonempty (LegendreTransformationOn (∅ : Set (EuclideanSpace ℝ (Fin 0))) f) from
      ⟨helperForText_26_4_0_2_emptyLegendreTransformationSource_finZero (f := f)⟩)

/-- Helper for Text 26.4.0.2: the specialization `n = 0`, `C = ∅` really satisfies every
hypothesis of the target theorem before the contradiction in the conclusion appears. -/
lemma helperForText_26_4_0_2_counterexampleHypotheses_finZero
    {f : (Fin 0 → ℝ) → ℝ} :
    Convex ℝ (∅ : Set (Fin 0 → ℝ)) ∧
      ConvexOn ℝ (∅ : Set (Fin 0 → ℝ)) f ∧
      Nonempty
        (LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
          (fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The empty set is convex in every real vector space.
    simpa using (convex_empty : Convex ℝ (∅ : Set (Fin 0 → ℝ)))
  · -- Convexity of `f` on the empty set is vacuous once the set argument is empty.
    constructor
    · simpa using (convex_empty : Convex ℝ (∅ : Set (Fin 0 → ℝ)))
    · intro x hx
      simp at hx
  · -- The previously constructed vacuous Legendre package supplies the final hypothesis.
    exact
      helperForText_26_4_0_2_nonemptyLegendreTransformation_finZero
        (f := fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x))

/-- Helper for Text 26.4.0.2: once specialized to `n = 0` and `C = ∅`, the theorem's
conclusion contradicts proper convexity before the Fenchel-conjugate clause is used. -/
lemma helperForText_26_4_0_2_emptyConclusionImpossible_finZero
    {f : (Fin 0 → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
      (fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x))) :
    ¬ ∃ F : (Fin 0 → ℝ) → EReal,
      ProperConvexERealFunction (F := (Fin 0 → ℝ)) F ∧
      LowerSemicontinuous F ∧
      (∀ x ∈ (∅ : Set (Fin 0 → ℝ)), F x = (f x : EReal)) ∧
      interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = (∅ : Set (Fin 0 → ℝ)) ∧
      ∀ xStar : legendreGradientImage
          ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
          (fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
        (L.conjFun xStar : EReal) =
          fenchelConjugate 0 F (xStar.1 : Fin 0 → ℝ) := by
  intro h
  rcases h with ⟨F, hF, _hLower, _hAgree, hInterior, _hFenchel⟩
  -- The specialized conclusion already contradicts the pointwise singleton-space obstruction.
  exact (helperForText_26_4_0_2_interior_effectiveDomain_ne_empty_finZero hF) hInterior

/-- Helper for Text 26.4.0.2: for a fixed zero-dimensional empty-source Legendre datum, the
specialized conclusion type is empty. -/
lemma helperForText_26_4_0_2_emptyConclusionTypeIsEmpty_finZero
    {f : (Fin 0 → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
      (fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x))) :
    IsEmpty
      (∃ F : (Fin 0 → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin 0 → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ (∅ : Set (Fin 0 → ℝ)), F x = (f x : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = (∅ : Set (Fin 0 → ℝ)) ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
            (fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate 0 F (xStar.1 : Fin 0 → ℝ)) := by
  refine ⟨?_⟩
  intro hConclusion
  -- Reuse the contradiction helper for the same specialized conclusion shape.
  exact helperForText_26_4_0_2_emptyConclusionImpossible_finZero (f := f) L hConclusion

/-- Helper for Text 26.4.0.2: the theorem shape already fails in the specialization `n = 0`,
`C = ∅`, before any universal quantification over dimensions is considered. -/
lemma helperForText_26_4_0_2_emptyCaseTheoremShapeFalse
    {f : (Fin 0 → ℝ) → ℝ}
    (hEmptyCase :
      ∀ L : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
          (fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
        ∃ F : (Fin 0 → ℝ) → EReal,
          ProperConvexERealFunction (F := (Fin 0 → ℝ)) F ∧
          LowerSemicontinuous F ∧
          (∀ x ∈ (∅ : Set (Fin 0 → ℝ)), F x = (f x : EReal)) ∧
          interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = (∅ : Set (Fin 0 → ℝ)) ∧
          ∀ xStar : legendreGradientImage
              ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
              (fun x : EuclideanSpace ℝ (Fin 0) => f ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
            (L.conjFun xStar : EReal) =
              fenchelConjugate 0 F (xStar.1 : Fin 0 → ℝ)) :
    False := by
  -- First produce an actual Legendre-transformation datum for the empty-source specialization.
  rcases helperForText_26_4_0_2_counterexampleHypotheses_finZero (f := f) with
    ⟨_hC_convex, _hf_convex, hLegendre⟩
  rcases hLegendre with ⟨L⟩
  -- Applying the specialized theorem shape to that datum yields the forbidden conclusion.
  exact helperForText_26_4_0_2_emptyConclusionImpossible_finZero (f := f) L (hEmptyCase L)

/-- Helper for Text 26.4.0.2: the concrete specialization `n = 0`, `C = ∅`, `f = 0`
already refutes the theorem's local conclusion shape. -/
lemma helperForText_26_4_0_2_zeroFunctionCounterexampleWitness_finZero :
    ∃ L : LegendreTransformationOn
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
        (fun x : EuclideanSpace ℝ (Fin 0) =>
          (fun _ : Fin 0 → ℝ => (0 : ℝ)) ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
      ¬ ∃ F : (Fin 0 → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin 0 → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ (∅ : Set (Fin 0 → ℝ)),
          F x = (((fun _ : Fin 0 → ℝ => (0 : ℝ)) x) : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = (∅ : Set (Fin 0 → ℝ)) ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
            (fun x : EuclideanSpace ℝ (Fin 0) =>
              (fun _ : Fin 0 → ℝ => (0 : ℝ)) ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate 0 F (xStar.1 : Fin 0 → ℝ) := by
  -- First extract an explicit Legendre datum from the empty-source zero-dimensional hypotheses.
  rcases helperForText_26_4_0_2_counterexampleHypotheses_finZero
      (f := fun _ : Fin 0 → ℝ => (0 : ℝ)) with
    ⟨_hC_convex, _hf_convex, hLegendre⟩
  rcases hLegendre with ⟨L⟩
  -- Then package the singleton-space obstruction as emptiness of the specialized conclusion.
  refine ⟨L, ?_⟩
  intro hConclusion
  exact
    (helperForText_26_4_0_2_emptyConclusionTypeIsEmpty_finZero
      (f := fun _ : Fin 0 → ℝ => (0 : ℝ)) L).false hConclusion

/-- Helper for Text 26.4.0.2: the concrete specialization `n = 0`, `C = ∅`, `f = 0`
already refutes the theorem's local conclusion shape. -/
lemma helperForText_26_4_0_2_zeroFunctionEmptyCaseFalse :
    ¬ (∀ L : LegendreTransformationOn
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
        (fun x : EuclideanSpace ℝ (Fin 0) =>
          (fun _ : Fin 0 → ℝ => (0 : ℝ)) ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
        ∃ F : (Fin 0 → ℝ) → EReal,
          ProperConvexERealFunction (F := (Fin 0 → ℝ)) F ∧
          LowerSemicontinuous F ∧
          (∀ x ∈ (∅ : Set (Fin 0 → ℝ)),
            F x = (((fun _ : Fin 0 → ℝ => (0 : ℝ)) x) : EReal)) ∧
          interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = (∅ : Set (Fin 0 → ℝ)) ∧
          ∀ xStar : legendreGradientImage
              ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
              (fun x : EuclideanSpace ℝ (Fin 0) =>
                (fun _ : Fin 0 → ℝ => (0 : ℝ)) ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
            (L.conjFun xStar : EReal) =
              fenchelConjugate 0 F (xStar.1 : Fin 0 → ℝ)) := by
  intro hEmptyCase
  -- The new counterexample witness packages the impossible local instance directly.
  rcases helperForText_26_4_0_2_zeroFunctionCounterexampleWitness_finZero with ⟨L, hImpossible⟩
  exact hImpossible (hEmptyCase L)

/-- Helper for Text 26.4.0.2: any proof of the theorem's universal statement yields the
forbidden zero-dimensional extension data after specializing to `n = 0` and `C = ∅`. -/
lemma helperForText_26_4_0_2_specializedWitness_finZero
    (hTarget :
      ∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ},
        Convex ℝ C →
        ConvexOn ℝ C f →
        ∀ L : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    ∃ L : LegendreTransformationOn
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
        (fun x : EuclideanSpace ℝ (Fin 0) =>
          (fun _ : Fin 0 → ℝ => (0 : ℝ)) ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
      ∃ F : (Fin 0 → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin 0 → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ (∅ : Set (Fin 0 → ℝ)),
          F x = (((fun _ : Fin 0 → ℝ => (0 : ℝ)) x) : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) F) = (∅ : Set (Fin 0 → ℝ)) ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' (∅ : Set (Fin 0 → ℝ)))
            (fun x : EuclideanSpace ℝ (Fin 0) =>
              (fun _ : Fin 0 → ℝ => (0 : ℝ)) ((EuclideanSpace.equiv (Fin 0) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate 0 F (xStar.1 : Fin 0 → ℝ) := by
  -- First realize the theorem's hypotheses in the zero-dimensional empty-source case.
  rcases helperForText_26_4_0_2_counterexampleHypotheses_finZero
      (f := fun _ : Fin 0 → ℝ => (0 : ℝ)) with
    ⟨hC_convex, hf_convex, hLegendre⟩
  rcases hLegendre with ⟨L⟩
  -- Then specialize the purported universal theorem statement to that concrete data.
  refine ⟨L, ?_⟩
  exact hTarget (n := 0) (C := ∅) (f := fun _ : Fin 0 → ℝ => (0 : ℝ)) hC_convex hf_convex L

/-- Helper for Text 26.4.0.2: the specialized zero-dimensional witness extracted from any
putative universal proof is already impossible, because its conclusion forces empty interior
effective domain on a singleton space. -/
lemma helperForText_26_4_0_2_specializedWitnessImpossible_finZero
    (hTarget :
      ∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ},
        Convex ℝ C →
        ConvexOn ℝ C f →
        ∀ L : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    False := by
  -- First extract the concrete zero-dimensional witness produced by the universal claim.
  rcases helperForText_26_4_0_2_specializedWitness_finZero hTarget with ⟨L, hWitness⟩
  -- Then invoke the singleton-space obstruction, which rules out that witness immediately.
  exact
    helperForText_26_4_0_2_emptyConclusionImpossible_finZero
      (f := fun _ : Fin 0 → ℝ => (0 : ℝ)) L hWitness

/-- Helper for Text 26.4.0.2: the theorem's full universal shape is refuted by the
zero-dimensional empty-set specialization. -/
lemma helperForText_26_4_0_2_universalStatementContradiction
    (hTarget :
      ∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ},
        Convex ℝ C →
        ConvexOn ℝ C f →
        ∀ L : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    False := by
  rcases helperForText_26_4_0_2_counterexampleHypotheses_finZero
      (f := fun _ : Fin 0 → ℝ => (0 : ℝ)) with
    ⟨hC_convex, hf_convex, _hLegendre⟩
  -- Route correction: specialize directly to the explicit `n = 0`, `C = ∅`, `f = 0` case.
  exact
    helperForText_26_4_0_2_zeroFunctionEmptyCaseFalse
      (fun L =>
        hTarget (n := 0) (C := ∅) (f := fun _ : Fin 0 → ℝ => (0 : ℝ))
          hC_convex hf_convex L)

/-- Helper for Text 26.4.0.2: the curried universal theorem shape and the declaration-form
signature are equivalent presentations of the same statement. -/
lemma helperForText_26_4_0_2_targetStatement_iff_declarationSignature :
    (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ},
        Convex ℝ C →
        ConvexOn ℝ C f →
        ∀ L : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) ↔
      (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
        (L : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  constructor
  · intro hTarget n C f hC_convex hf_convex L
    -- Reinterpret the curried implication chain at the current explicit parameters.
    exact hTarget hC_convex hf_convex L
  · intro hDecl n C f hC_convex hf_convex L
    -- Curry the explicit declaration-form arguments back into implication form.
    exact hDecl hC_convex hf_convex L

/-- Helper for Text 26.4.0.2: the curried universal theorem statement is empty for the same
zero-dimensional empty-set reason as the declaration-form signature. -/
lemma helperForText_26_4_0_2_targetStatementIsEmpty :
    IsEmpty
      (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ},
        Convex ℝ C →
        ConvexOn ℝ C f →
        ∀ L : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  refine ⟨?_⟩
  intro hTarget
  -- The zero-dimensional empty-set specialization already contradicts this curried statement.
  exact helperForText_26_4_0_2_universalStatementContradiction hTarget

/-- Helper for Text 26.4.0.2: the full universally quantified theorem statement is false,
because the specialization `n = 0`, `C = ∅` satisfies the hypotheses but violates the
conclusion. -/
lemma helperForText_26_4_0_2_targetStatementFalse :
    ¬ (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ},
        Convex ℝ C →
        ConvexOn ℝ C f →
        ∀ L : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  intro hTarget
  -- Repackage the universal statement as an empty type, then eliminate its hypothetical inhabitant.
  exact helperForText_26_4_0_2_targetStatementIsEmpty.false hTarget

/-- Helper for Text 26.4.0.2: any declaration-form proof specializes to the impossible
zero-dimensional empty-set case, for every `f : (Fin 0 → ℝ) → ℝ`. -/
lemma helperForText_26_4_0_2_false_of_declarationSignature_finZero
    (hDecl : ∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
      (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
      (L : LegendreTransformationOn
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
        (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
        ∃ F : (Fin n → ℝ) → EReal,
          ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
          LowerSemicontinuous F ∧
          (∀ x ∈ C, F x = (f x : EReal)) ∧
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
          ∀ xStar : legendreGradientImage
              ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
              (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
            (L.conjFun xStar : EReal) =
              fenchelConjugate n F (xStar.1 : Fin n → ℝ))
    (f : (Fin 0 → ℝ) → ℝ) :
    False := by
  -- Specialize the theorem hypotheses to the empty zero-dimensional source.
  rcases helperForText_26_4_0_2_counterexampleHypotheses_finZero (f := f) with
    ⟨hC_convex, hf_convex, hLegendre⟩
  rcases hLegendre with ⟨L⟩
  -- The extracted witness forces an impossible empty interior effective domain.
  exact
    helperForText_26_4_0_2_emptyConclusionImpossible_finZero (f := f) L
      (hDecl (n := 0) (C := ∅) (f := f) hC_convex hf_convex L)

/-- Helper for Text 26.4.0.2: the theorem's declaration-form signature is already refuted by
the same zero-dimensional empty-set specialization. -/
lemma helperForText_26_4_0_2_declarationSignatureFalse :
    ¬ (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
        (L : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  intro hDecl
  -- Convert back to the curried universal statement and reuse its already-packaged contradiction.
  exact
    helperForText_26_4_0_2_targetStatementFalse
      (helperForText_26_4_0_2_targetStatement_iff_declarationSignature.2 hDecl)

/-- Helper for Text 26.4.0.2: the exact declaration type of the target theorem is empty,
because the zero-dimensional empty-set specialization already contradicts it. -/
lemma helperForText_26_4_0_2_declarationSignatureIsEmpty :
    IsEmpty
      (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
        (L : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  -- Repackage the earlier negated declaration signature as an `IsEmpty` witness.
  refine ⟨?_⟩
  intro hDecl
  exact helperForText_26_4_0_2_declarationSignatureFalse hDecl

/-- Helper for Text 26.4.0.2: any inhabitant of the declaration-form universal statement would
specialize immediately to the current local theorem goal. -/
lemma helperForText_26_4_0_2_localGoal_of_declarationSignature
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hDecl :
      ∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
        (L' : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L'.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    ∃ F : (Fin n → ℝ) → EReal,
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
      LowerSemicontinuous F ∧
      (∀ x ∈ C, F x = (f x : EReal)) ∧
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
      ∀ xStar : legendreGradientImage
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
        (L.conjFun xStar : EReal) =
          fenchelConjugate n F (xStar.1 : Fin n → ℝ) := by
  -- Evaluate the declaration-form universal term at the current parameters.
  exact hDecl hC_convex hf_convex L

/-- Helper for Text 26.4.0.2: for the current local parameters, the remaining declaration-based
proof skeleton is completely explicit. The exact declaration signature is empty, but any repaired
inhabitant of that signature would specialize to the present local goal. -/
lemma helperForText_26_4_0_2_localReductionRouteData
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    IsEmpty
      (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
        (L' : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L'.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) ∧
      ((∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
          (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
          (L' : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
            ∃ F : (Fin n → ℝ) → EReal,
              ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
              LowerSemicontinuous F ∧
              (∀ x ∈ C, F x = (f x : EReal)) ∧
              interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
              ∀ xStar : legendreGradientImage
                  ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                  (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
                (L'.conjFun xStar : EReal) =
                  fenchelConjugate n F (xStar.1 : Fin n → ℝ)) →
        ∃ F : (Fin n → ℝ) → EReal,
          ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
          LowerSemicontinuous F ∧
          (∀ x ∈ C, F x = (f x : EReal)) ∧
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
          ∀ xStar : legendreGradientImage
              ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
              (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
            (L.conjFun xStar : EReal) =
              fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  -- The declaration-form source type is already empty by the explicit `Fin 0` counterexample.
  refine ⟨helperForText_26_4_0_2_declarationSignatureIsEmpty, ?_⟩
  intro hDecl
  -- Evaluating that repaired declaration term at the present parameters recovers the local goal.
  exact
    helperForText_26_4_0_2_localGoal_of_declarationSignature
      hC_convex hf_convex L hDecl

/-- Helper for Text 26.4.0.2: in the current local theorem context, the exact declaration-form
source type is still uninhabited, so no proof can be obtained merely by specializing the current
false universal header. -/
lemma helperForText_26_4_0_2_noLocalDeclarationSignature
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    ¬ (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
        (L' : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L'.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  intro hDecl
  -- First extract the already-proved emptiness of the declaration-form source type.
  have hRouteData :=
    helperForText_26_4_0_2_localReductionRouteData hC_convex hf_convex L
  -- Then apply that emptiness witness to the supposed declaration-form proof term.
  exact hRouteData.1.false hDecl

/-- Helper for Text 26.4.0.2: in the current local theorem context, there cannot simultaneously
be a declaration-form universal proof term and a witness for the present goal, because the
declaration-form source type is already empty. -/
lemma helperForText_26_4_0_2_noLocalDeclarationSpecializationPair
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    IsEmpty
      ((∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
          (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
          (L' : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
            ∃ F : (Fin n → ℝ) → EReal,
              ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
              LowerSemicontinuous F ∧
              (∀ x ∈ C, F x = (f x : EReal)) ∧
              interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
              ∀ xStar : legendreGradientImage
                  ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                  (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
                (L'.conjFun xStar : EReal) =
                  fenchelConjugate n F (xStar.1 : Fin n → ℝ)) ∧
        (∃ F : (Fin n → ℝ) → EReal,
          ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
          LowerSemicontinuous F ∧
          (∀ x ∈ C, F x = (f x : EReal)) ∧
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
          ∀ xStar : legendreGradientImage
              ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
              (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
            (L.conjFun xStar : EReal) =
              fenchelConjugate n F (xStar.1 : Fin n → ℝ))) := by
  refine ⟨?_⟩
  intro hPair
  -- The first component alone already contradicts the previously isolated empty source type.
  exact
    (helperForText_26_4_0_2_localReductionRouteData hC_convex hf_convex L).1.false
      hPair.1

/-- Helper for Text 26.4.0.2: once a local witness for the present goal is fixed, the
declaration-form universal route is still unavailable, because combining the two would inhabit
the already-empty specialization pair type. -/
lemma helperForText_26_4_0_2_localWitness_blocks_declarationRoute
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    (∃ F : (Fin n → ℝ) → EReal,
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
      LowerSemicontinuous F ∧
      (∀ x ∈ C, F x = (f x : EReal)) ∧
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
      ∀ xStar : legendreGradientImage
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
        (L.conjFun xStar : EReal) =
          fenchelConjugate n F (xStar.1 : Fin n → ℝ)) →
      ¬ (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
          (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
          (L' : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
            ∃ F : (Fin n → ℝ) → EReal,
              ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
              LowerSemicontinuous F ∧
              (∀ x ∈ C, F x = (f x : EReal)) ∧
              interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
              ∀ xStar : legendreGradientImage
                  ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                  (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
                (L'.conjFun xStar : EReal) =
                  fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  intro hWitness hDecl
  -- Pair the declaration-form source term with the fixed local witness.
  exact
    (helperForText_26_4_0_2_noLocalDeclarationSpecializationPair hC_convex hf_convex L).false
      ⟨hDecl, hWitness⟩

/-- Helper for Text 26.4.0.2: in the current local theorem context, the exact local goal is
what any repaired declaration-form proof would specialize to, but the declaration-form source
type is already empty. This isolates the remaining blocker to an upstream repair of the theorem
statement rather than to any further local decomposition. -/
lemma helperForText_26_4_0_2_localGoalRouteSummary
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    ((∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
        (L' : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L'.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) →
      ∃ F : (Fin n → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ C, F x = (f x : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate n F (xStar.1 : Fin n → ℝ)) ∧
      ¬ (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
          (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
          (L' : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
            ∃ F : (Fin n → ℝ) → EReal,
              ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
              LowerSemicontinuous F ∧
              (∀ x ∈ C, F x = (f x : EReal)) ∧
              interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
              ∀ xStar : legendreGradientImage
                  ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                  (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
                (L'.conjFun xStar : EReal) =
                  fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  constructor
  · intro hDecl
    -- Any repaired declaration-form proof would specialize directly to the current local goal.
    exact
      helperForText_26_4_0_2_localGoal_of_declarationSignature
        hC_convex hf_convex L hDecl
  · -- The declaration-form source type is already ruled out by the zero-dimensional obstruction.
    exact helperForText_26_4_0_2_noLocalDeclarationSignature hC_convex hf_convex L


end Section26
end Chap05
