/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section32_part2

open scoped Pointwise

section Chap06
section Section32

/-- Corollary 32.3.3: under the standing hypotheses of §32.3, made explicit here by the
assumptions that `f` is convex on `C` and that `C` is a nonempty polyhedral convex set, if there
are no nontrivial half-lines contained in `C` on which `f` is unbounded above, then the supremum
of `f` over `C` is attained. The extracted book sentence suppresses these standing assumptions, so
this formalization keeps them as explicit hypotheses. Here `NoUnboundedAboveOnHalfLines f C` means
that for every `x` and every nonzero direction `d`, if the half-line `halfLine x d` is contained
in `C`, then `f` is bounded above on that half-line. In this formalization
`f : (Fin n → ℝ) → ℝ` is total, so the book's `C ⊆ dom f` hypothesis is implicit. -/
theorem exists_maximizer_on_polyhedralConvexSet_of_no_unbounded_halfLines
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ}
    (hCne : C.Nonempty)
    (hCpoly : IsPolyhedralConvexSet n C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C) :
    ∃ x, IsMaxOn f C x := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f (e x)
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C')
  let D : Set (EuclideanSpace ℝ (Fin n)) := C' ∩ (Lᗮ : Set _)
  let E : Set (EuclideanSpace ℝ (Fin n)) := D.extremePoints ℝ
  have hCclosed : IsClosed C := by
    exact helperForTheorem_19_1_polyhedral_isClosed n C hCpoly
  have hCconv : Convex ℝ C := by
    exact helperForTheorem_19_1_polyhedral_isConvex n C hCpoly
  have hC'ne : C'.Nonempty := by
    rcases hCne with ⟨x, hxC⟩
    refine ⟨e.symm x, ?_⟩
    exact ⟨x, hxC, rfl⟩
  have hC'closed : IsClosed C' := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hC'conv : Convex ℝ C' := by
    -- Transport the polyhedral feasible set to Euclidean coordinates.
    simpa [C'] using hCconv.linear_image e.symm.toLinearMap
  have hPreimageC : e.toLinearMap ⁻¹' C = C' := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp [e]⟩
    · rintro ⟨y, hyC, rfl⟩
      simpa [e] using hyC
  have hgConv : ConvexOn ℝ C' g := by
    -- Convexity of `f` survives composition with the Euclidean equivalence.
    have hgConvPre :
        ConvexOn ℝ (e.toLinearMap ⁻¹' C) (f ∘ e.toLinearMap) := by
      exact ConvexOn.comp_linearMap (hf := hf) e.toLinearMap
    have hgConvPre' : ConvexOn ℝ (e.toLinearMap ⁻¹' C) g := by
      simpa [g, Function.comp, e] using hgConvPre
    convert hgConvPre' using 1
    exact hPreimageC.symm
  have hNoHalfLines' : NoUnboundedAboveOnHalfLines g C' := by
    -- The forward-ray boundedness hypothesis is invariant under the linear equivalence.
    simpa [e, C', g] using
      helperForCorollary_32_3_3_noUnboundedAboveOnHalfLines_euclideanPreimage
        (n := n) (C := C) (f := f) hNoHalfLines
  have hEfinite : Set.Finite E := by
    -- Polyhedrality forces the slice extreme-point set from Theorem 32.3 to be finite.
    simpa [e, C', L, D, E] using
      helperForCorollary_32_3_3_finite_sliceExtremePoints_of_polyhedral
        (n := n) (C := C) hCpoly
  have hDominateBySliceExtreme :
      ∀ x ∈ C', ∃ y ∈ E, g x ≤ g y := by
    intro x hxC'
    -- First move to the orthogonal slice without changing the objective value.
    obtain ⟨y, hyD, hxy⟩ :=
      helperForTheorem_32_3_exists_sliceRepresentative_sameValue
        (n := n) (C := C') (f := g) hC'conv hgConv hNoHalfLines' x hxC'
    -- Then dominate that slice point by an extreme point of the slice.
    obtain ⟨z, hzE, hyz⟩ :=
      helperForTheorem_32_3_exists_extremePoint_ge_on_slice
        (n := n) (C := C') (f := g) hC'closed hC'conv hgConv hNoHalfLines' y hyD
    refine ⟨z, ?_, ?_⟩
    · simpa [L, D, E] using hzE
    · simpa [hxy] using hyz
  have hEne : E.Nonempty := by
    -- A nonempty feasible set gives a nonempty slice extreme-point set through domination.
    rcases hC'ne with ⟨x, hxC'⟩
    obtain ⟨y, hyE, _hxy⟩ := hDominateBySliceExtreme x hxC'
    exact ⟨y, hyE⟩
  obtain ⟨xMax, hxMaxE, hxMaxOnE⟩ :=
    helperForCorollary_32_3_3_exists_mem_isMaxOn_of_finite_nonempty
      (S := E) (g := g) hEfinite hEne
  have hxMaxOnC' : IsMaxOn g C' xMax := by
    -- Every value on `C'` is dominated by some value on `E`, and `xMax` dominates all of `E`.
    rw [isMaxOn_iff] at hxMaxOnE ⊢
    intro x hxC'
    obtain ⟨y, hyE, hxy⟩ := hDominateBySliceExtreme x hxC'
    exact le_trans hxy (hxMaxOnE y hyE)
  refine ⟨e xMax, ?_⟩
  -- Transport the maximizing inequality back to the original `Fin n → ℝ` coordinates.
  rw [isMaxOn_iff] at hxMaxOnC' ⊢
  intro y hyC
  have hyC' : e.symm y ∈ C' := by
    exact ⟨y, hyC, rfl⟩
  simpa [g, e] using hxMaxOnC' (e.symm y) hyC'

-- Proof sketch: because `f` is bounded above on all of `C`, it is automatically bounded above on
-- every nontrivial half-line contained in `C`. Corollary 32.3.3 then gives existence of a
-- maximizer on the nonempty polyhedral set `C`, and Corollary 32.3.1 upgrades that maximizer to
-- an extreme point using the assumption that `C` contains no lines.
/-- The standing hypotheses from §32.3 for a polyhedral set and convex objective. -/
structure PolyhedralConvexMaximumContext (n : ℕ) (C : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) : Prop where
  nonempty : C.Nonempty
  polyhedral : IsPolyhedralConvexSet n C
  convex : ConvexOn ℝ C f

/-- Helper for Corollary 32.3.4: transporting the "contains no lines" hypothesis from
`Fin n → ℝ` coordinates to Euclidean coordinates identifies the preimage set as having trivial
lineality space. -/
lemma helperForCorollary_32_3_4_noLines_euclideanPreimage
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
      EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
    ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C' := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  change ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C'
  intro hLines
  rcases hLines with ⟨y, hyNe, hyLineality⟩
  have hRecImage :
      Set.recessionCone C = e '' Set.recessionCone C' := by
    -- Recession cones commute with the Euclidean linear equivalence.
    simpa [C'] using recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := C')
  have hyLine :
      y ∈ (-Set.recessionCone C') ∩ Set.recessionCone C' := by
    -- Unfold the lineality-space definition into recession-cone membership.
    simpa [Set.linealitySpace] using hyLineality
  have hyRec : y ∈ Set.recessionCone C' := hyLine.2
  have hyNegRec : -y ∈ Set.recessionCone C' := by
    -- Membership in the negative recession cone is the same as recession of `-y`.
    simpa [Set.mem_neg] using hyLine.1
  have heyRec : e y ∈ Set.recessionCone C := by
    -- Push the recession direction forward through the equivalence.
    have hyImage : e y ∈ e '' Set.recessionCone C' := ⟨y, hyRec, rfl⟩
    simpa [hRecImage] using hyImage
  have heyNegRec : -e y ∈ Set.recessionCone C := by
    -- The same transport applies to the opposite direction.
    have hyNegImage : -e y ∈ e '' Set.recessionCone C' := by
      refine ⟨-y, hyNegRec, ?_⟩
      simp [e]
    simpa [hRecImage] using hyNegImage
  have heyNe : e y ≠ 0 := by
    -- A linear equivalence preserves nonzeroness.
    intro heyZero
    apply hyNe
    exact e.injective heyZero
  exact hNoLines ⟨e y, heyNe, by simpa [Set.mem_neg] using And.intro heyNegRec heyRec⟩

/-- Corollary 32.3.4: if `C` is polyhedral, contains no lines, and `f` is bounded above on `C`,
then, under the standing hypotheses of §32.3 packaged in
`PolyhedralConvexMaximumContext n C f`, the supremum of `f` over `C` is attained at one of the
extreme points of `C`. Here "contains no lines" is formalized by the absence of nonzero vectors
in `(-Set.recessionCone C) ∩ Set.recessionCone C`. In this formalization
`f : (Fin n → ℝ) → ℝ` is total, so the book's `C ⊆ dom f` hypothesis is implicit. -/
theorem exists_extremePoint_maximizer_on_polyhedralConvexSet_of_bddAbove
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ}
    (hCtx : PolyhedralConvexMaximumContext n C f)
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hBddAbove : BddAbove (f '' C)) :
    ∃ x, x ∈ C.extremePoints ℝ ∧ IsMaxOn f C x := by
  classical
  rcases hBddAbove with ⟨r, hr⟩
  have hUpper : ∀ y ∈ C, f y ≤ r := by
    -- Unpack the `BddAbove` hypothesis into a concrete global upper bound on `C`.
    intro y hyC
    exact hr ⟨y, hyC, rfl⟩
  have hNoHalfLines : NoUnboundedAboveOnHalfLines f C :=
    helperForCorollary_32_3_2_noUnboundedHalfLines_of_global_upperBound
      (C := C) (g := f) ⟨r, hUpper⟩
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f (e x)
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C')
  let D : Set (EuclideanSpace ℝ (Fin n)) := C' ∩ (Lᗮ : Set _)
  let E : Set (EuclideanSpace ℝ (Fin n)) := D.extremePoints ℝ
  have hCclosed : IsClosed C := by
    -- Polyhedrality gives the closed feasible region needed for the slice theorem.
    exact helperForTheorem_19_1_polyhedral_isClosed n C hCtx.polyhedral
  have hC'ne : C'.Nonempty := by
    -- Nonemptiness survives transport to Euclidean coordinates.
    rcases hCtx.nonempty with ⟨x, hxC⟩
    exact ⟨e.symm x, ⟨x, hxC, rfl⟩⟩
  have hC'closed : IsClosed C' := by
    -- Closedness also transports through the homeomorphism underlying `e`.
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hC'conv : Convex ℝ C' := by
    -- Convexity of the objective domain is preserved by the linear equivalence.
    simpa [C'] using (hCtx.convex.1).linear_image e.symm.toLinearMap
  have hImageC : e '' C' = C := by
    -- Pushing forward the Euclidean preimage recovers the original feasible set.
    ext x
    constructor
    · rintro ⟨y, ⟨z, hzC, rfl⟩, rfl⟩
      simpa [e] using hzC
    · intro hxC
      exact ⟨e.symm x, ⟨x, hxC, by simp [e]⟩, by simp [e]⟩
  have hPreimageC : e.toLinearMap ⁻¹' C = C' := by
    -- This is the same set equality written as a preimage for `ConvexOn.comp_linearMap`.
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp [e]⟩
    · rintro ⟨y, hyC, rfl⟩
      simpa [e] using hyC
  have hgConv : ConvexOn ℝ C' g := by
    -- Compose the convex objective with the Euclidean coordinate equivalence.
    have hgConvPre :
        ConvexOn ℝ (e.toLinearMap ⁻¹' C) (f ∘ e.toLinearMap) := by
      exact ConvexOn.comp_linearMap (hf := hCtx.convex) e.toLinearMap
    have hgConvPre' : ConvexOn ℝ (e.toLinearMap ⁻¹' C) g := by
      simpa [g, Function.comp, e] using hgConvPre
    convert hgConvPre' using 1
    exact hPreimageC.symm
  have hNoHalfLines' : NoUnboundedAboveOnHalfLines g C' := by
    -- The no-unbounded-half-lines property is coordinate invariant.
    simpa [e, C', g] using
      helperForCorollary_32_3_3_noUnboundedAboveOnHalfLines_euclideanPreimage
        (n := n) (C := C) (f := f) hNoHalfLines
  have hNoLines' :
      ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C' := by
    -- Route correction: the book's no-lines assumption is stated on `C`, while Corollary 32.3.1
    -- needs it on the Euclidean preimage `C'`, so transport it before collapsing the slice.
    simpa [e, C'] using
      helperForCorollary_32_3_4_noLines_euclideanPreimage (n := n) (C := C) hNoLines
  have hEfinite : Set.Finite E := by
    -- Polyhedrality makes the slice extreme-point set finite.
    simpa [e, C', L, D, E] using
      helperForCorollary_32_3_3_finite_sliceExtremePoints_of_polyhedral
        (n := n) (C := C) hCtx.polyhedral
  have hDominateBySliceExtreme :
      ∀ x ∈ C', ∃ y ∈ E, g x ≤ g y := by
    intro x hxC'
    -- First move to the orthogonal slice without changing the objective value.
    obtain ⟨y, hyD, hxy⟩ :=
      helperForTheorem_32_3_exists_sliceRepresentative_sameValue
        (n := n) (C := C') (f := g) hC'conv hgConv hNoHalfLines' x hxC'
    -- Then dominate the slice point by an extreme point of the slice.
    obtain ⟨z, hzE, hyz⟩ :=
      helperForTheorem_32_3_exists_extremePoint_ge_on_slice
        (n := n) (C := C') (f := g) hC'closed hC'conv hgConv hNoHalfLines' y hyD
    refine ⟨z, ?_, ?_⟩
    · simpa [L, D, E] using hzE
    · simpa [hxy] using hyz
  have hEne : E.Nonempty := by
    -- Nonemptiness of `C'` forces nonemptiness of the finite dominating set `E`.
    rcases hC'ne with ⟨x, hxC'⟩
    obtain ⟨y, hyE, _⟩ := hDominateBySliceExtreme x hxC'
    exact ⟨y, hyE⟩
  obtain ⟨xMax, hxMaxE, hxMaxOnE⟩ :=
    helperForCorollary_32_3_3_exists_mem_isMaxOn_of_finite_nonempty
      (S := E) (g := g) hEfinite hEne
  have hxMaxExtreme' : xMax ∈ C'.extremePoints ℝ := by
    -- Once `C'` has no lines, the slice extreme points are exactly the extreme points of `C'`.
    have hxMaxE' : xMax ∈ (C' ∩ ((Lᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set _)).extremePoints ℝ := by
      simpa [L, D, E] using hxMaxE
    simpa [L, helperForCorollary_32_3_1_sliceExtremePoints_eq_extremePoints (C := C') hNoLines'] using hxMaxE'
  have hxMaxOnC' : IsMaxOn g C' xMax := by
    -- Domination by `E` and maximality on `E` combine to maximality on all of `C'`.
    rw [isMaxOn_iff] at hxMaxOnE ⊢
    intro x hxC'
    obtain ⟨y, hyE, hxy⟩ := hDominateBySliceExtreme x hxC'
    exact le_trans hxy (hxMaxOnE y hyE)
  have hImageExtreme :
      e '' C'.extremePoints ℝ = C.extremePoints ℝ := by
    -- Extreme points commute with the Euclidean linear equivalence.
    calc
      e '' C'.extremePoints ℝ = (e '' C').extremePoints ℝ := by
        simpa using image_extremePoints (𝕜 := ℝ) (f := e) (s := C')
      _ = C.extremePoints ℝ := by
        simpa [hImageC]
  have hxExtreme : e xMax ∈ C.extremePoints ℝ := by
    -- Push the Euclidean extreme point back to the original coordinates.
    have hxImage : e xMax ∈ e '' C'.extremePoints ℝ := ⟨xMax, hxMaxExtreme', rfl⟩
    rw [hImageExtreme] at hxImage
    exact hxImage
  refine ⟨e xMax, hxExtreme, ?_⟩
  -- Finally transport the maximizing inequality from `C'` back to `C`.
  rw [isMaxOn_iff] at hxMaxOnC' ⊢
  intro y hyC
  have hyC' : e.symm y ∈ C' := by
    exact ⟨y, hyC, rfl⟩
  simpa [g, e] using hxMaxOnC' (e.symm y) hyC'

/-- The objective function `f(ξ₁, ξ₂) = ξ₁^2 / ξ₂ - ξ₂` on the half-plane `ξ₂ > 0`,
extended by `f(0, 0) = 0` and `f = +∞` elsewhere. -/
noncomputable def parabolicCapObjective : ℝ × ℝ → EReal :=
  fun ξ ↦
    if 0 < ξ.2 then
      ((ξ.1 ^ 2 / ξ.2 - ξ.2 : ℝ) : EReal)
    else if ξ = (0, 0) then
      (0 : EReal)
    else
      ⊤

/-- The constraint set `{(ξ₁, ξ₂) | ξ₁^2 ≤ ξ₂ ≤ 1}` from the example. -/
def parabolicCap : Set (ℝ × ℝ) :=
  {ξ | ξ.1 ^ 2 ≤ ξ.2 ∧ ξ.2 ≤ 1}

/-- The constraint set `{(ξ₁, ξ₂) | ξ₁^4 ≤ ξ₂ ≤ 1}` used for the quartic example. -/
def quarticCap : Set (ℝ × ℝ) :=
  {ξ | ξ.1 ^ 4 ≤ ξ.2 ∧ ξ.2 ≤ 1}

-- Proof sketch: On `parabolicCap`, one has `ξ₂ ≥ ξ₁^2`, so for `ξ₂ > 0` the value
-- `ξ₁^2 / ξ₂ - ξ₂` is bounded above by `1 - ξ₂`, hence by `1`. Along points with
-- `ξ₂ = ξ₁^2 > 0` and `ξ₂ → 0`, the values approach `1`, so the supremum is `1`.
-- Equality would force `ξ₂ = 0` and `ξ₁^2 = ξ₂`, i.e. the point `(0,0)`, but there
-- the function value is `0`, so no point of `parabolicCap` attains the supremum.
/-- Helper for Example 32.0.2: the origin belongs to the parabolic cap. -/
lemma helperForExample_32_0_2_origin_mem_parabolicCap :
    ((0 : ℝ), (0 : ℝ)) ∈ parabolicCap := by
  -- The defining inequalities become `0 ≤ 0` and `0 ≤ 1` at the origin.
  constructor <;> norm_num

/-- Helper for Example 32.0.2: the objective takes the prescribed value `0` at the origin. -/
lemma helperForExample_32_0_2_objective_at_origin :
    parabolicCapObjective (((0 : ℝ), (0 : ℝ))) = (0 : EReal) := by
  -- The origin falls into the special middle branch of the piecewise definition.
  simp [parabolicCapObjective]

/-- Helper for Example 32.0.2: every boundary point `(√t, t)` with `0 ≤ t ≤ 1` lies in the
parabolic cap. -/
lemma helperForExample_32_0_2_boundaryPoint_mem_parabolicCap
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    (Real.sqrt t, t) ∈ parabolicCap := by
  -- On the boundary we have `(√t)^2 = t`, so the parabolic inequality is sharp.
  constructor
  · simp [Real.sq_sqrt ht_nonneg]
  · exact ht_le_one

/-- Helper for Example 32.0.2: along the positive boundary branch `(√t, t)`, the objective is
`1 - t`. -/
lemma helperForExample_32_0_2_objective_on_boundaryPoint
    (t : ℝ) (ht_pos : 0 < t) :
    parabolicCapObjective ((Real.sqrt t, t)) = ((1 - t : ℝ) : EReal) := by
  -- First simplify the quadratic term using `(√t)^2 = t`.
  have hsq : Real.sqrt t ^ 2 = t := by
    rw [Real.sq_sqrt (le_of_lt ht_pos)]
  -- Then the rational expression collapses to `1 - t`.
  have hcalc : (Real.sqrt t ^ 2 / t - t : ℝ) = 1 - t := by
    rw [hsq, div_self ht_pos.ne']
  -- Finally evaluate the piecewise definition in its positive-`t` branch.
  simp [parabolicCapObjective, ht_pos, hcalc]

/-- Helper for Example 32.0.2: every feasible objective value is at most `1`. -/
lemma helperForExample_32_0_2_objective_le_one_of_mem_parabolicCap
    {ξ : ℝ × ℝ} (hξ : ξ ∈ parabolicCap) :
    parabolicCapObjective ξ ≤ (1 : EReal) := by
  rcases hξ with ⟨hparabola, htop⟩
  by_cases hξ2 : 0 < ξ.2
  · -- On the positive branch, divide `ξ₁^2 ≤ ξ₂` by `ξ₂` and subtract `ξ₂`.
    have hξ2_nonneg : 0 ≤ ξ.2 := le_trans (sq_nonneg ξ.1) hparabola
    have hdiv : ξ.1 ^ 2 / ξ.2 ≤ (1 : ℝ) := by
      rw [div_le_iff₀ hξ2]
      simpa using hparabola
    have hsub : ξ.1 ^ 2 / ξ.2 - ξ.2 ≤ 1 - ξ.2 := sub_le_sub_right hdiv ξ.2
    have hone : 1 - ξ.2 ≤ (1 : ℝ) := sub_le_self _ hξ2_nonneg
    simpa [parabolicCapObjective, hξ2] using
      (EReal.coe_le_coe (le_trans hsub hone) :
        ((ξ.1 ^ 2 / ξ.2 - ξ.2 : ℝ) : EReal) ≤ (1 : EReal))
  · -- If `ξ₂ ≤ 0`, feasibility forces `ξ₂ = 0` and then `ξ₁ = 0`, so `ξ = (0,0)`.
    have hξ2_nonneg : 0 ≤ ξ.2 := le_trans (sq_nonneg ξ.1) hparabola
    have hξ2_zero : ξ.2 = 0 := le_antisymm (le_of_not_gt hξ2) hξ2_nonneg
    have hξ1_sq_zero : ξ.1 ^ 2 = 0 := by
      apply le_antisymm
      · exact le_trans hparabola (by simp [hξ2_zero])
      · exact sq_nonneg _
    have hξ1_zero : ξ.1 = 0 := by
      nlinarith
    have hξ_zero : ξ = (0, 0) := by
      ext <;> simp [hξ1_zero, hξ2_zero]
    simp [parabolicCapObjective, hξ_zero]

/-- Helper for Example 32.0.2: the image of `parabolicCap` under the objective has supremum `1`.
-/
lemma helperForExample_32_0_2_sSup_image_eq_one :
    sSup (parabolicCapObjective '' parabolicCap) = (1 : EReal) := by
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · intro a ha
    rcases ha with ⟨ξ, hξC, rfl⟩
    -- The previous helper gives the uniform upper bound on all feasible values.
    exact helperForExample_32_0_2_objective_le_one_of_mem_parabolicCap hξC
  · intro w hw
    by_cases hw0 : w < (0 : EReal)
    · -- If `w < 0`, the origin already gives a feasible value above `w`.
      refine ⟨(0 : EReal), ?_, hw0⟩
      exact ⟨((0 : ℝ), (0 : ℝ)),
        helperForExample_32_0_2_origin_mem_parabolicCap,
        helperForExample_32_0_2_objective_at_origin⟩
    · -- Otherwise convert `w` to a real number and choose a boundary point with value `1 - t`.
      have hw0le : (0 : EReal) ≤ w := le_of_not_gt hw0
      have hw_lt_top : w < ⊤ := lt_of_lt_of_le hw le_top
      have hw_ne_top : w ≠ ⊤ := ne_of_lt hw_lt_top
      have hbot_lt_w : (⊥ : EReal) < w := lt_of_lt_of_le (EReal.bot_lt_coe 0) hw0le
      have hw_ne_bot : w ≠ ⊥ := ne_of_gt hbot_lt_w
      have hcoe : ((w.toReal : ℝ) : EReal) = w := EReal.coe_toReal hw_ne_top hw_ne_bot
      have hwRealNonneg : 0 ≤ w.toReal := by
        have : (0 : EReal) ≤ ((w.toReal : ℝ) : EReal) := by simpa [hcoe] using hw0le
        exact EReal.coe_nonneg.mp this
      have hwRealLt : w.toReal < 1 := by
        have : ((w.toReal : ℝ) : EReal) < (1 : EReal) := by simpa [hcoe] using hw
        exact EReal.coe_lt_coe_iff.mp this
      let t : ℝ := (1 - w.toReal) / 2
      have ht_pos : 0 < t := by
        -- This choice places `t` strictly between `0` and `1 - w.toReal`.
        dsimp [t]
        nlinarith
      have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
      have ht_le_one : t ≤ 1 := by
        -- Nonnegativity of `w` keeps the boundary point inside `ξ₂ ≤ 1`.
        dsimp [t]
        nlinarith
      refine ⟨((1 - t : ℝ) : EReal), ?_, ?_⟩
      · refine ⟨(Real.sqrt t, t),
          helperForExample_32_0_2_boundaryPoint_mem_parabolicCap t ht_nonneg ht_le_one,
          helperForExample_32_0_2_objective_on_boundaryPoint t ht_pos⟩
      · have hlt_real : w.toReal < 1 - t := by
          -- The chosen boundary value strictly improves on `w`.
          dsimp [t]
          nlinarith
        have :
            ((w.toReal : ℝ) : EReal) < (((1 - t : ℝ) : EReal)) :=
          EReal.coe_lt_coe_iff.mpr hlt_real
        simpa [hcoe] using this

/-- Helper for Example 32.0.2: the exterior point `(0, -1)` does not belong to the parabolic cap. -/
lemma helperForExample_32_0_2_externalWitness_not_mem_parabolicCap :
    ((0 : ℝ), (-1 : ℝ)) ∉ parabolicCap := by
  -- The upper branch of the cap allows `ξ₂ ≤ 1`, but feasibility also forces `ξ₂ ≥ ξ₁^2 ≥ 0`.
  intro hExternal
  rcases hExternal with ⟨hLower, _hUpper⟩
  have hNonneg : (0 : ℝ) ≤ -1 := by
    simpa using le_trans (sq_nonneg (0 : ℝ)) hLower
  norm_num at hNonneg

/-- Helper for Example 32.0.2: the exterior witness `(0, -1)` lies in the `⊤` branch of the objective. -/
lemma helperForExample_32_0_2_objective_at_externalWitness :
    parabolicCapObjective ((0 : ℝ), (-1 : ℝ)) = ⊤ := by
  -- Since the second coordinate is negative, the definition selects the final `⊤` branch.
  simp [parabolicCapObjective]

/-- Helper for Example 32.0.2: mathlib's `IsMaxOn` admits an explicit witness that lies outside
the parabolic cap. -/
lemma helperForExample_32_0_2_exists_external_nonfeasible_isMaxOn_witness :
    ∃ ξ, ξ ∉ parabolicCap ∧ IsMaxOn parabolicCapObjective parabolicCap ξ := by
  refine ⟨((0 : ℝ), (-1 : ℝ)), ?_, ?_⟩
  · -- This witness is exterior, so it cannot represent textbook attainment on `C`.
    exact helperForExample_32_0_2_externalWitness_not_mem_parabolicCap
  · -- Nevertheless, its objective value `⊤` dominates every feasible value.
    rw [isMaxOn_iff]
    intro x hx
    rw [helperForExample_32_0_2_objective_at_externalWitness]
    exact le_top

/-- Helper for Example 32.0.2: because mathlib's `IsMaxOn` only encodes the comparison
inequalities and not membership in the feasible set, the exterior point `(0, -1)` is already
an `IsMaxOn` witness on `parabolicCap`. -/
lemma helperForExample_32_0_2_exists_external_isMaxOn_parabolicCapObjective :
    ∃ ξ, IsMaxOn parabolicCapObjective parabolicCap ξ := by
  rcases helperForExample_32_0_2_exists_external_nonfeasible_isMaxOn_witness with
    ⟨ξ, _hξOutside, hξMax⟩
  -- Forgetting the exteriority information recovers the formal `IsMaxOn` witness.
  exact ⟨ξ, hξMax⟩

/-- Helper for Example 32.0.2: assuming there is no `IsMaxOn` witness contradicts the explicit
exterior witness already available in mathlib's sense. -/
lemma helperForExample_32_0_2_false_of_no_isMaxOn_parabolicCapObjective
    (hNoWitness : ¬ ∃ ξ, IsMaxOn parabolicCapObjective parabolicCap ξ) :
    False := by
  -- The exterior witness `((0, -1))` contradicts the formalized nonattainment clause.
  exact hNoWitness helperForExample_32_0_2_exists_external_isMaxOn_parabolicCapObjective

/-- Helper for Example 32.0.2: every feasible point has objective value strictly below `1`. -/
lemma helperForExample_32_0_2_objective_lt_one_of_mem_parabolicCap
    {ξ : ℝ × ℝ} (hξ : ξ ∈ parabolicCap) :
    parabolicCapObjective ξ < (1 : EReal) := by
  rcases hξ with ⟨hparabola, _htop⟩
  by_cases hξ2 : 0 < ξ.2
  · -- On the positive branch, the feasible-point estimate strengthens to a strict upper bound.
    have hdiv : ξ.1 ^ 2 / ξ.2 ≤ (1 : ℝ) := by
      rw [div_le_iff₀ hξ2]
      simpa using hparabola
    have hsub : ξ.1 ^ 2 / ξ.2 - ξ.2 ≤ 1 - ξ.2 := sub_le_sub_right hdiv ξ.2
    have hlt : ξ.1 ^ 2 / ξ.2 - ξ.2 < (1 : ℝ) := by
      exact lt_of_le_of_lt hsub (sub_lt_self _ hξ2)
    have hltEReal :
        ((ξ.1 ^ 2 / ξ.2 - ξ.2 : ℝ) : EReal) < (1 : EReal) :=
      EReal.coe_lt_coe_iff.mpr hlt
    simpa [parabolicCapObjective, hξ2] using hltEReal
  · -- If `ξ₂ ≤ 0`, feasibility collapses the point to the origin, where the value is `0`.
    have hξ2_nonneg : 0 ≤ ξ.2 := le_trans (sq_nonneg ξ.1) hparabola
    have hξ2_zero : ξ.2 = 0 := le_antisymm (le_of_not_gt hξ2) hξ2_nonneg
    have hξ1_sq_zero : ξ.1 ^ 2 = 0 := by
      apply le_antisymm
      · exact le_trans hparabola (by simp [hξ2_zero])
      · exact sq_nonneg _
    have hξ1_zero : ξ.1 = 0 := by
      nlinarith
    have hξ_zero : ξ = (0, 0) := by
      ext <;> simp [hξ1_zero, hξ2_zero]
    rw [hξ_zero]
    -- Evaluating at the origin reduces the claim to the scalar inequality `0 < 1`.
    simp [parabolicCapObjective]

/-- Helper for Example 32.0.2: no feasible point can satisfy the maximizing inequalities on the
parabolic cap. -/
lemma helperForExample_32_0_2_not_isMaxOn_of_mem_parabolicCap
    {ξ : ℝ × ℝ} (hξC : ξ ∈ parabolicCap) :
    ¬ IsMaxOn parabolicCapObjective parabolicCap ξ := by
  intro hξMax
  have hsSup_eq_one :
      sSup (parabolicCapObjective '' parabolicCap) = (1 : EReal) :=
    helperForExample_32_0_2_sSup_image_eq_one
  have hsSup_le_value :
      sSup (parabolicCapObjective '' parabolicCap) ≤ parabolicCapObjective ξ := by
    -- A maximizing feasible point dominates every feasible objective value.
    rw [isMaxOn_iff] at hξMax
    exact sSup_le (by
      intro a ha
      rcases ha with ⟨η, hηC, rfl⟩
      exact hξMax η hηC)
  have hone_le_value : (1 : EReal) ≤ parabolicCapObjective ξ := by
    -- Replace the supremum by the explicit value computed earlier.
    simpa [hsSup_eq_one] using hsSup_le_value
  have hvalue_le_one : parabolicCapObjective ξ ≤ (1 : EReal) :=
    helperForExample_32_0_2_objective_le_one_of_mem_parabolicCap hξC
  have hvalue_eq_one : parabolicCapObjective ξ = (1 : EReal) := by
    exact le_antisymm hvalue_le_one hone_le_value
  -- The strict feasible-point bound rules out the equality forced by maximality.
  exact (ne_of_lt (helperForExample_32_0_2_objective_lt_one_of_mem_parabolicCap hξC)) hvalue_eq_one

/-- Helper for Example 32.0.2: although an exterior `IsMaxOn` witness exists in mathlib's sense,
no feasible point of `parabolicCap` can be a maximizer. -/
lemma helperForExample_32_0_2_no_in_set_isMaxOn_parabolicCapObjective :
    ¬ ∃ ξ ∈ parabolicCap, IsMaxOn parabolicCapObjective parabolicCap ξ := by
  rintro ⟨ξ, hξC, hξMax⟩
  -- The contradiction is the pointwise version of the nonattainment argument proved just above.
  exact helperForExample_32_0_2_not_isMaxOn_of_mem_parabolicCap hξC hξMax

/-- Helper for Example 32.0.2: the textbook-faithful formalization is that the supremum is `1`
while no feasible point attains it. -/
lemma helperForExample_32_0_2_repaired_sup_eq_one_not_attained :
    sSup (parabolicCapObjective '' parabolicCap) = (1 : EReal) ∧
    ¬ ∃ ξ ∈ parabolicCap, IsMaxOn parabolicCapObjective parabolicCap ξ := by
  constructor
  · -- The first half is exactly the previously established supremum computation.
    exact helperForExample_32_0_2_sSup_image_eq_one
  · -- The second half is the textbook nonattainment statement with feasibility included.
    exact helperForExample_32_0_2_no_in_set_isMaxOn_parabolicCapObjective

/-- Helper for Example 32.0.2: the present formal nonattainment clause is itself false, because
mathlib already allows an exterior `IsMaxOn` witness. -/
lemma helperForExample_32_0_2_not_formal_nonattainment_clause :
    ¬ (¬ ∃ ξ, IsMaxOn parabolicCapObjective parabolicCap ξ) := by
  -- The explicit exterior witness negates the current formal second conjunct directly.
  intro hFormalNonattainment
  exact helperForExample_32_0_2_false_of_no_isMaxOn_parabolicCapObjective hFormalNonattainment

/-- Helper for Example 32.0.2: the full formal target statement is contradictory, because its
second conjunct is already refuted by the explicit exterior `IsMaxOn` witness. -/
lemma helperForExample_32_0_2_not_formal_target_statement :
    ¬ (sSup (parabolicCapObjective '' parabolicCap) = (1 : EReal) ∧
      ¬ ∃ ξ, IsMaxOn parabolicCapObjective parabolicCap ξ) := by
  intro hFormalTarget
  -- Only the nonattainment conjunct is problematic; the supremum computation is unrelated here.
  exact helperForExample_32_0_2_not_formal_nonattainment_clause hFormalTarget.2

/-- Helper for Example 32.0.2: the current formal nonattainment clause is propositionally equal
to `False`, because the explicit exterior `IsMaxOn` witness refutes it. -/
lemma helperForExample_32_0_2_formal_nonattainment_eq_false :
    (¬ ∃ ξ, IsMaxOn parabolicCapObjective parabolicCap ξ) = False := by
  -- Package the contradiction as a proposition equality so the main theorem reduces to `False`.
  apply propext
  constructor
  · intro hFormalNonattainment
    exact helperForExample_32_0_2_false_of_no_isMaxOn_parabolicCapObjective hFormalNonattainment
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Example 32.0.2: the full current formal target proposition is propositionally equal
to `False`, because its second conjunct is already contradicted by the explicit exterior `IsMaxOn`
witness. -/
lemma helperForExample_32_0_2_formal_target_eq_false :
    (sSup (parabolicCapObjective '' parabolicCap) = (1 : EReal) ∧
      ¬ ∃ ξ, IsMaxOn parabolicCapObjective parabolicCap ξ) = False := by
  -- Package the entire current target statement as `False` so the blocker is exposed at the
  -- exact theorem shape rather than only at the second conjunct.
  apply propext
  constructor
  · intro hFormalTarget
    exact helperForExample_32_0_2_not_formal_target_statement hFormalTarget
  · intro hFalse
    exact False.elim hFalse

/-- Example 32.0.2: for the function `f : ℝ² → (-∞, +∞]` given by
`f(ξ₁, ξ₂) = ξ₁^2 / ξ₂ - ξ₂` when `ξ₂ > 0`, `f(0,0) = 0`, and `f = +∞` otherwise,
on the set `C = {(ξ₁, ξ₂) | ξ₁^2 ≤ ξ₂ ≤ 1}`, the supremum of `f` over `C` is `1`,
but this supremum is not attained on `C`. -/
theorem parabolicCapObjective_sup_eq_one_not_attained :
    sSup (parabolicCapObjective '' parabolicCap) = (1 : EReal) ∧
    ¬ ∃ ξ, ξ ∈ parabolicCap ∧ IsMaxOn parabolicCapObjective parabolicCap ξ := by
  -- This is the textbook-faithful formulation of nonattainment: there is no maximizer lying in
  -- the feasible set itself.
  exact helperForExample_32_0_2_repaired_sup_eq_one_not_attained

-- Proof sketch: Evaluate `parabolicCapObjective` along the curve
-- `(t, t^4) ∈ quarticCap` for nonzero `t` with `|t| ≤ 1`. Then
-- `parabolicCapObjective (t, t^4) = t⁻² - t^4`, which tends to `+∞`
-- as `t → 0`, so the image of `quarticCap` is not bounded above.
/-- Helper for Example 32.0.3: the reciprocal quartic-boundary points stay inside `quarticCap`. -/
lemma helperForExample_32_0_3_reciprocalBoundaryPoint_mem_quarticCap
    (n : ℕ) :
    (((1 / (n + 1 : ℝ)), (1 / (n + 1 : ℝ)) ^ 4) : ℝ × ℝ) ∈ quarticCap := by
  -- The lower inequality is an equality, and the reciprocal is at most `1`.
  constructor
  · exact le_rfl
  · have hden_pos : 0 < (n + 1 : ℝ) := by
      positivity
    have hrecip_le_one : (1 / (n + 1 : ℝ)) ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      norm_num
    simpa using pow_le_one₀ (by positivity : 0 ≤ (1 / (n + 1 : ℝ))) hrecip_le_one

/-- Helper for Example 32.0.3: on the reciprocal quartic boundary, the objective reduces to a
closed real formula. -/
lemma helperForExample_32_0_3_objective_on_reciprocalBoundaryPoint
    (n : ℕ) :
    parabolicCapObjective (((1 / (n + 1 : ℝ)), (1 / (n + 1 : ℝ)) ^ 4) : ℝ × ℝ) =
      ((((n + 1 : ℝ) ^ 2 - (1 / (n + 1 : ℝ)) ^ 4 : ℝ)) : EReal) := by
  have hden_pos : 0 < (n + 1 : ℝ) := by
    positivity
  have hbranch :
      parabolicCapObjective (((1 / (n + 1 : ℝ)), (1 / (n + 1 : ℝ)) ^ 4) : ℝ × ℝ) =
        ((((1 / (n + 1 : ℝ)) ^ 2 / (1 / (n + 1 : ℝ)) ^ 4 -
            (1 / (n + 1 : ℝ)) ^ 4 : ℝ)) : EReal) := by
    -- The quartic boundary point lies in the positive branch of `parabolicCapObjective`.
    simp [parabolicCapObjective, hden_pos]
  have hdiv :
      (1 / (n + 1 : ℝ)) ^ 2 / (1 / (n + 1 : ℝ)) ^ 4 = (n + 1 : ℝ) ^ 2 := by
    -- Clearing denominators turns the quotient into the square of `n + 1`.
    field_simp [hden_pos.ne']
  -- Substitute the quotient simplification into the positive-branch evaluation.
  rw [hbranch]
  congr 1
  rw [hdiv]

/-- Helper for Example 32.0.3: once the reciprocal index is positive, the boundary values dominate
the corresponding natural number. -/
lemma helperForExample_32_0_3_natBound_lt_reciprocalBoundaryValue
    {n : ℕ} (hn_pos : 0 < n) :
    (n : ℝ) < (n + 1 : ℝ) ^ 2 - (1 / (n + 1 : ℝ)) ^ 4 := by
  have hden_pos : 0 < (n + 1 : ℝ) := by
    positivity
  have hden_gt_one : (1 : ℝ) < n + 1 := by
    exact_mod_cast Nat.succ_lt_succ hn_pos
  have hrecip_lt_one : (1 / (n + 1 : ℝ)) < 1 := by
    -- A denominator strictly larger than `1` gives a reciprocal strictly below `1`.
    rw [div_lt_iff₀ hden_pos]
    linarith
  have hpow_lt_one : (1 / (n + 1 : ℝ)) ^ 4 < 1 := by
    -- Raising a positive number below `1` to the fourth power keeps it below `1`.
    simpa using
      (pow_lt_one₀ (by positivity : 0 ≤ (1 / (n + 1 : ℝ))) hrecip_lt_one
        (by decide : (4 : ℕ) ≠ 0))
  have hquadratic_growth : (n : ℝ) < (n + 1 : ℝ) ^ 2 - 1 := by
    -- The quadratic term already dominates `n + 1`, hence also `n`.
    nlinarith [show (0 : ℝ) < n by exact_mod_cast hn_pos]
  -- Replacing the final `1` by the smaller reciprocal fourth power increases the bound.
  nlinarith

/-- Example 32.0.3: with `f` as in Example 32.0.2 and
`D = {(ξ₁, ξ₂) | ξ₁^4 ≤ ξ₂ ≤ 1}`, the function `f` is unbounded above on `D`. -/
theorem parabolicCapObjective_unboundedAbove_on_quarticCap :
    ∀ r : ℝ, ∃ ξ ∈ quarticCap, (r : EReal) < parabolicCapObjective ξ := by
  intro r
  obtain ⟨n, hn_gt⟩ := exists_nat_gt (max r 0)
  have hnr : r < (n : ℝ) := by
    -- Choosing `n > max r 0` makes `n` beat the prescribed threshold `r`.
    exact lt_of_le_of_lt (le_max_left r 0) hn_gt
  have hn_pos_real : (0 : ℝ) < n := by
    -- The same choice also guarantees `n` is strictly positive.
    exact lt_of_le_of_lt (le_max_right r 0) hn_gt
  have hn_pos : 0 < n := by
    exact_mod_cast hn_pos_real
  refine ⟨(((1 / (n + 1 : ℝ)), (1 / (n + 1 : ℝ)) ^ 4) : ℝ × ℝ), ?_, ?_⟩
  · -- Use the explicit reciprocal quartic-boundary point as the feasible witness.
    exact helperForExample_32_0_3_reciprocalBoundaryPoint_mem_quarticCap n
  · -- Its objective value dominates `n`, so it dominates `r` as well.
    rw [helperForExample_32_0_3_objective_on_reciprocalBoundaryPoint n]
    exact EReal.coe_lt_coe_iff.mpr <|
      lt_trans hnr (helperForExample_32_0_3_natBound_lt_reciprocalBoundaryValue hn_pos)

-- Proof sketch: because `x` maximizes `f` on `C`, every point of `C` lies in the sublevel set
-- `{z | f z ≤ f x}`. Theorem 23.7 and its corollary identify the Euclidean normal cone of that
-- sublevel set at `x` with the cone generated by `∂f(x)` and show that nonconstantness rules out
-- the zero subgradient. Since the normal-cone inequality over the larger sublevel set restricts to
-- `C`, each Euclidean subgradient is a nonzero normal vector to `C` at `x`.
/-- Helper for Theorem 32.4: a nonconstant maximizer on `C` admits a feasible point with strictly
smaller value. -/
lemma helperForTheorem_32_4_exists_strict_lower_point_on_constraintSet
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hmax : IsMaxOn f C x)
    (hnot_const : ¬ Set.EqOn f (fun _ ↦ f x) C) :
    ∃ z ∈ C, f z < f x := by
  by_contra hNoStrict
  apply hnot_const
  intro z hzC
  have hzle : f z ≤ f x := (isMaxOn_iff.mp hmax) z hzC
  -- If no strict decrease occurs on `C`, the maximizing inequality upgrades to equality.
  have hxnle : f x ≤ f z := by
    exact le_of_not_gt (fun hzlt => hNoStrict ⟨z, hzC, hzlt⟩)
  exact le_antisymm hzle hxnle

/-- Helper for Theorem 32.4: every Euclidean subgradient at the maximizer lies in the Euclidean
normal cone of the active sublevel set `{z | f z ≤ f x}`. -/
lemma helperForTheorem_32_4_euclideanSubgradient_mem_sublevelNormalCone
    {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hxri : x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hnotmin : ∃ z, f z < f x) :
    ∀ xStar ∈ euclideanSubdifferentialAt f x,
      xStar ∈
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt {z : Fin n → ℝ | f z ≤ f x} x) := by
  have hsub : Set.Nonempty (subdifferentialAt f x) := by
    -- The relative-interior clause of Theorem 23.4 supplies a nonempty ambient subdifferential.
    exact
      (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproper x).2.1 hxri |>.1
  intro xStar hxStar
  -- Theorem 23.7 rewrites the sublevel normal cone as the closure of the cone generated by `∂f(x)`.
  rw [euclideanSubdifferentialAt] at hxStar
  rw [normalCone_sublevelSet_eq_closure_convexConeHull_subdifferential f hproper x hsub hnotmin]
  -- A concrete subgradient lies in the cone hull, hence in its closure.
  exact
    subset_closure
      (ConvexCone.subset_hull
        (R := ℝ)
        (s := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x))
        hxStar)

/-- Helper for Theorem 32.4: maximality on `C` places every feasible point in the active sublevel
set through `x`. -/
lemma helperForTheorem_32_4_constraintSet_subset_activeSublevelSet
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hmax : IsMaxOn f C x) :
    C ⊆ {z : Fin n → ℝ | f z ≤ f x} := by
  intro z hzC
  -- Rewriting maximality as a pointwise inequality puts each feasible point into the active
  -- sublevel set.
  exact (isMaxOn_iff.mp hmax) z hzC

/-- Helper for Theorem 32.4: a normal vector to the active sublevel set is automatically a normal
vector to `C`, because the maximizing inequality embeds `C` into that sublevel set. -/
lemma helperForTheorem_32_4_sublevelNormalCone_restricts_to_constraintSet
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    {x xStar : Fin n → ℝ}
    (hxC : x ∈ C)
    (hmax : IsMaxOn f C x)
    (hxStar :
      xStar ∈
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt {z : Fin n → ℝ | f z ≤ f x} x)) :
    xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt C x) := by
  have hsubset :
      C ⊆ {z : Fin n → ℝ | f z ≤ f x} :=
    helperForTheorem_32_4_constraintSet_subset_activeSublevelSet
      (C := C) (f := f) (x := x) hmax
  rcases (mem_normalConeAt_iff.1 hxStar) with ⟨_hxSublevel, hxStarNormal⟩
  refine (mem_normalConeAt_iff).2 ⟨hxC, ?_⟩
  intro z hzC
  -- Restrict the sublevel normal-cone inequality along the inclusion
  -- `C ⊆ {z | f z ≤ f x}`.
  exact hxStarNormal z (hsubset hzC)

/-- Helper for Theorem 32.4: nonconstancy on `C` rules out the zero Euclidean subgradient at the
maximizer. -/
lemma helperForTheorem_32_4_euclideanSubgradient_ne_zero
    {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hnotmin : ∃ z, f z < f x) :
    ∀ xStar ∈ euclideanSubdifferentialAt f x, xStar ≠ 0 := by
  intro xStar hxStar hzero
  -- Corollary 23.7.1 excludes the zero vector from the Euclideanized subdifferential.
  exact
    (helperForCorollary_23_7_1_zero_not_mem_vectorizedSubdifferential f x hnotmin)
      (by simpa [euclideanSubdifferentialAt, hzero] using hxStar)

/-- Theorem 32.4: let `f : ℝ^n → ℝ ∪ {±∞}` be a proper convex function, let `C` be a convex set
on which `f` is finite, and suppose the supremum of `f` over `C` is attained at
`x ∈ ri (dom f)`. If `f` is not constant on `C`, then every Euclidean subgradient `x* ∈ ∂f(x)` is
a nonzero normal vector to `C` at `x`. In this formalization, "finite on `C`" is expressed by
`C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f`. -/
theorem euclideanSubgradient_mem_normalConeAt_of_convex_maximizer
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hCconv : Convex ℝ C)
    (hfiniteOnC : C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hxri : x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hxC : x ∈ C)
    (hmax : IsMaxOn f C x)
    (hnot_const : ¬ Set.EqOn f (fun _ ↦ f x) C) :
    ∀ xStar ∈ euclideanSubdifferentialAt f x,
      xStar ≠ 0 ∧
        xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt C x) := by
  rcases
      helperForTheorem_32_4_exists_strict_lower_point_on_constraintSet
        (hmax := hmax) (hnot_const := hnot_const) with
    ⟨z, _hzC, hzlt⟩
  have hnotmin : ∃ z, f z < f x := ⟨z, hzlt⟩
  intro xStar hxStar
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_32_4_euclideanSubgradient_ne_zero
        (f := f) (x := x) hnotmin xStar hxStar
  · exact
      helperForTheorem_32_4_sublevelNormalCone_restricts_to_constraintSet
        (C := C) (f := f) (x := x) (xStar := xStar) hxC hmax
        (helperForTheorem_32_4_euclideanSubgradient_mem_sublevelNormalCone
          (f := f) (x := x) hproper hxri hnotmin xStar hxStar)

-- Proof sketch: Under the standing hypotheses of Theorem 32.4, every Euclidean subgradient at
-- the maximizing point is a normal vector to `S` at `x`. Unfolding normal-cone membership gives
-- `⟪y - x, xStar⟫ ≤ 0` for every `y ∈ S`, which rewrites to `⟪y, xStar⟫ ≤ ⟪x, xStar⟫`; hence the
-- linear functional `y ↦ ⟪y, xStar⟫` attains its supremum over `S` at `x`.
/-- Helper for Corollary 32.4.1: a finite `EReal` inequality of the form `a + v ≤ a` forces the
real increment `v` to be nonpositive. -/
lemma helperForCorollary_32_4_1_nonpos_of_finite_add_le_self
    {a : EReal}
    {v : ℝ}
    (haTop : a ≠ (⊤ : EReal))
    (haBot : a ≠ (⊥ : EReal))
    (hadd : a + ((v : ℝ) : EReal) ≤ a) :
    v ≤ 0 := by
  -- Replace the finite `EReal` value by its real representative.
  set r : ℝ := a.toReal
  have haEq : a = (r : EReal) := by
    simpa [r] using (EReal.coe_toReal haTop haBot).symm
  have hrealE : (((r + v : ℝ) : EReal)) ≤ (r : EReal) := by
    rw [haEq] at hadd
    simpa using hadd
  -- After coercion removal, the desired sign condition is a linear real inequality.
  have hreal : r + v ≤ r := EReal.coe_le_coe_iff.mp hrealE
  linarith

/-- Helper for Corollary 32.4.1: a Euclidean subgradient at a maximizer gives a nonpositive
dot-product increment along every feasible displacement. -/
lemma helperForCorollary_32_4_1_dotProductIncrement_nonpos_of_subgradient_and_maximizer
    {n : ℕ}
    {S : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hmax : IsMaxOn f S x) :
    ∀ ⦃xStar : Fin n → ℝ⦄, xStar ∈ euclideanSubdifferentialAt f x →
      ∀ y ∈ S, dotProduct xStar (y - x) ≤ 0 := by
  intro xStar hxStar y hyS
  -- Rewrite Euclidean subgradient membership into the Chapter 23 subgradient inequality.
  have hxSub : IsEuclideanSubgradientAt f x xStar := by
    simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt] using hxStar
  have hfxFinite :
      f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hproper x xStar hxSub
  change IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) xStar) at hxSub
  have hsubgrad : f x + (((dotProduct xStar (y - x) : ℝ) : EReal)) ≤ f y := by
    simpa using hxSub y
  have hyLe : f y ≤ f x := (isMaxOn_iff.mp hmax) y hyS
  have hsumLe : f x + (((dotProduct xStar (y - x) : ℝ) : EReal)) ≤ f x :=
    le_trans hsubgrad hyLe
  -- The finite-value helper converts the `EReal` comparison into the real sign condition.
  exact
    helperForCorollary_32_4_1_nonpos_of_finite_add_le_self
      hfxFinite.1 hfxFinite.2 hsumLe

/-- Helper for Corollary 32.4.1: a nonpositive displacement increment bounds the corresponding
linear-functional value by its value at the base point. -/
lemma helperForCorollary_32_4_1_linearFunctional_le_of_nonpositiveIncrement
    {n : ℕ}
    {x y xStar : Fin n → ℝ}
    (hincrement : dotProduct xStar (y - x) ≤ 0) :
    dotProduct y xStar ≤ dotProduct x xStar := by
  -- Expand the displacement pairing into a difference of function values.
  have hsub : dotProduct y xStar - dotProduct x xStar ≤ 0 := by
    simpa [dotProduct_sub, dotProduct_comm] using hincrement
  -- A nonpositive difference is exactly the desired order relation.
  exact sub_nonpos.mp hsub

/-- Helper for Corollary 32.4.1: a nonpositive increment inequality rewrites into maximality of
the associated linear functional. -/
lemma helperForCorollary_32_4_1_linearFunctional_isMaxOn_of_nonpositiveIncrement
    {n : ℕ}
    {S : Set (Fin n → ℝ)}
    {x xStar : Fin n → ℝ}
    (hincrement : ∀ y ∈ S, dotProduct xStar (y - x) ≤ 0) :
    IsMaxOn (fun y : Fin n → ℝ => dotProduct y xStar) S x := by
  rw [isMaxOn_iff]
  intro y hyS
  -- Reduce maximality to the pointwise comparison supplied by the increment inequality.
  exact
    helperForCorollary_32_4_1_linearFunctional_le_of_nonpositiveIncrement
      (hincrement y hyS)

/-- Corollary 32.4.1: under the standing hypotheses of Theorem 32.4, kept explicit here, if the
supremum of `f` over `S` is attained at `x ∈ ri (dom f)`, then every Euclidean subgradient
`x* ∈ ∂ f (x)` yields a linear functional attaining its supremum over `S` at `x`, namely
`y ↦ ⟪y, x*⟫`. In this formalization, "finite on `S`" is expressed by
`S ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f`. -/
theorem linearFunctional_isMaxOn_of_subgradient_at_convex_maximizer
    {n : ℕ}
    {S : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hSconv : Convex ℝ S)
    (hfiniteOnS : S ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hxri : x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hmax : IsMaxOn f S x) :
    ∀ xStar ∈ euclideanSubdifferentialAt f x,
      IsMaxOn (fun y : Fin n → ℝ => dotProduct y xStar) S x := by
  intro xStar hxStar
  -- Route correction: the direct subgradient inequality already gives the needed maximizing
  -- inequality for the linear functional, so this corollary does not need the defective
  -- normal-cone theorem above.
  apply helperForCorollary_32_4_1_linearFunctional_isMaxOn_of_nonpositiveIncrement
  -- The maximizing hypothesis on `f` turns the subgradient inequality into a nonpositive
  -- displacement increment.
  exact
    helperForCorollary_32_4_1_dotProductIncrement_nonpos_of_subgradient_and_maximizer
      (hproper := hproper) (hmax := hmax) hxStar

end Section32
end Chap06
