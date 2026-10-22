/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part22

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Corollary 35.8.1: the packed quotient along a second-block basis vector is exactly
the quotient of the honest second slice `y ↦ K u y` along the corresponding coordinate basis. -/
lemma helperForCorollary_35_8_1_packedSecondBasisQuotient_eq_secondSliceBasisQuotient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
        (Pi.single (Fin.natAdd m j) (1 : ℝ)) t =
      directionalDifferenceQuotientAt (K u) v (Pi.single j (1 : ℝ)) t := by
  have hdir :
      (Fin.append (0 : Fin m → ℝ) (Pi.single j (1 : ℝ)) : Fin (m + n) → ℝ) =
        (Pi.single (Fin.natAdd m j) (1 : ℝ) : Fin (m + n) → ℝ) := by
    -- A pure second-block packed direction is exactly the basis vector indexed by `Fin.natAdd`.
    calc
      (Fin.append (0 : Fin m → ℝ) (Pi.single j (1 : ℝ)) : Fin (m + n) → ℝ) =
          Fin.append
            (fun i : Fin m =>
              (Pi.single (Fin.natAdd m j) (1 : ℝ) : Fin (m + n) → ℝ) (Fin.castAdd n i))
            (fun j' : Fin n =>
              (Pi.single (Fin.natAdd m j) (1 : ℝ) : Fin (m + n) → ℝ) (Fin.natAdd m j')) := by
            apply congrArg₂ Fin.append
            · funext x
              have hne : Fin.castAdd n x ≠ Fin.natAdd m j := by
                intro h
                have hval := congrArg Fin.val h
                simp [Fin.natAdd, Fin.castAdd] at hval
                omega
              simp [Pi.single_apply, hne]
            · funext x
              simp [Pi.single_apply]
      _ = (Pi.single (Fin.natAdd m j) (1 : ℝ) : Fin (m + n) → ℝ) := by
            simpa using
              (Fin.append_castAdd_natAdd
                (f := (Pi.single (Fin.natAdd m j) (1 : ℝ) : Fin (m + n) → ℝ)))
  -- Rewrite the packed basis vector as a pure second-block direction and reuse the slice helper.
  simpa [hdir] using
    (helperForTheorem_35_8_directionalDifferenceQuotient_secondSlice
      (K := K) u v (Pi.single j (1 : ℝ)) t)

/-- Helper for Corollary 35.8.1: a finite packed first-block coordinate partial transfers to the
corresponding coordinate partial of the reflected convex slice `x ↦ -K (-x) v`. -/
lemma helperForCorollary_35_8_1_reflectedFirstSliceCoordinatePartial_of_packedFirstCoordinatePartial
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (i : Fin m) (L : ℝ)
    (hpartial :
      HasCoordinatePartialDerivativeAt (packedSaddleKernel K) (Fin.append u v)
        (Fin.castAdd n i) (L : EReal)) :
    HasCoordinatePartialDerivativeAt (fun x : Fin m → ℝ => -K (-x) v) (-u) i (L : EReal) := by
  let e : Fin m → ℝ := Pi.single i (1 : ℝ)
  let ePacked : Fin (m + n) → ℝ := Pi.single (Fin.castAdd n i) (1 : ℝ)
  have hPackedFinite :
      packedSaddleKernel K (Fin.append u v) ≠ (⊤ : EReal) ∧
        packedSaddleKernel K (Fin.append u v) ≠ (⊥ : EReal) := by
    -- Evaluating the packed kernel at the base point recovers `K u v`.
    simpa [packedSaddleKernel] using hFinite
  have hrightPackedNeg :
      Filter.Tendsto
        (directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v) (-ePacked))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((-L : ℝ) : EReal))) := by
    have hbilat :
        HasBilateralDirectionalDerivativeAt (packedSaddleKernel K) (Fin.append u v) ePacked :=
      ⟨(L : EReal), by simpa [ePacked] using hpartial.1, by simpa [ePacked] using hpartial.2⟩
    rcases
        ((bilateralDirectionalDerivative_iff_exists_neg_direction
          (f := packedSaddleKernel K) (x := Fin.append u v) (y := ePacked) hPackedFinite).2).1 hbilat
      with ⟨M, hMeq, hnegRight⟩
    have hML : M = (L : EReal) := by
      exact tendsto_nhds_unique hMeq (by simpa [ePacked] using hpartial.1)
    -- The packed left limit along the `i`th first-block axis becomes a right limit along `-e_i`.
    simpa [ePacked, hML] using hnegRight
  have hright :
      Filter.Tendsto
        (directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) e)
        (𝓝[>] (0 : ℝ))
        (𝓝 (L : EReal)) := by
    have hrightNegated :
        Filter.Tendsto
          (fun t =>
            -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v) (-ePacked) t)
          (𝓝[>] (0 : ℝ))
          (𝓝 (L : EReal)) := by
      simpa using hrightPackedNeg.neg
    -- Rewrite the reflected quotient as the negative packed quotient along the opposite axis.
    have hpointRight :
        ∀ t : ℝ,
          directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) e t =
            -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v) (-ePacked) t := by
      intro t
      simpa [e, ePacked] using
        (helperForCorollary_35_8_1_reflectedFirstBasisQuotient_eq_negPackedNegativeBasisQuotient
          (K := K) (u := u) (v := v) hFinite i t)
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun t => (hpointRight t).symm) hrightNegated
  have hRefFinite :
      (fun x : Fin m → ℝ => -K (-x) v) (-u) ≠ (⊤ : EReal) ∧
        (fun x : Fin m → ℝ => -K (-x) v) (-u) ≠ (⊥ : EReal) := by
    -- The reflected slice stays finite at the recentered base point.
    simpa using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase
        (K := K) (u := u) (v := v) hFinite
  have hrightNeg :
      Filter.Tendsto
        (directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) (-e))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((-L : ℝ) : EReal))) := by
    have hPackedNegated :
        Filter.Tendsto
          (fun t =>
            -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v) ePacked t)
          (𝓝[>] (0 : ℝ))
          (𝓝 (((-L : ℝ) : EReal))) := by
      simpa [ePacked] using hpartial.1.neg
    -- The same quotient identity with direction `-e_i` transports the positive packed limit.
    have hpointNeg :
        ∀ t : ℝ,
          directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) (-e) t =
            -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v) ePacked t := by
      intro t
      simpa [e, ePacked] using
        (helperForCorollary_35_8_1_reflectedNegativeBasisQuotient_eq_negPackedPositiveBasisQuotient
          (K := K) (u := u) (v := v) hFinite i t)
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun t => (hpointNeg t).symm) hPackedNegated
  have hleft :
      Filter.Tendsto
        (directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) e)
        (𝓝[<] (0 : ℝ))
        (𝓝 (L : EReal)) := by
    -- Convert the right limit along `-e_i` into the left limit along `e_i`.
    have hleft_from_right :=
      (bilateralDirectionalDerivative_iff_exists_neg_direction
        (f := fun x : Fin m → ℝ => -K (-x) v) (x := -u) (y := e) hRefFinite).1
    simpa using hleft_from_right (((-L : ℝ) : EReal)) hrightNeg
  -- Put the reflected-axis basis vector back into the coordinate-partial definition.
  simpa [e] using And.intro hright hleft

/-- Helper for Corollary 35.8.1: finite packed coordinate partials induce coordinate partials on
the reflected first slice and the ordinary second slice needed for the Chapter 25 slice theorem. -/
lemma helperForCorollary_35_8_1_sliceCoordinatePartials_of_packedCoordinatePartials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartials :
      ∀ j : Fin (m + n), ∃ L : ℝ,
        HasCoordinatePartialDerivativeAt
          (packedSaddleKernel K) (Fin.append u v) j (L : EReal)) :
    (∀ i : Fin m, ∃ L : ℝ,
      HasCoordinatePartialDerivativeAt (fun x : Fin m → ℝ => -K (-x) v) (-u) i (L : EReal)) ∧
    (∀ j : Fin n, ∃ L : ℝ, HasCoordinatePartialDerivativeAt (K u) v j (L : EReal)) := by
  constructor
  · intro i
    rcases hpartials (Fin.castAdd n i) with ⟨L, hL⟩
    -- The first block is handled by the reflected first-slice transport proved above.
    exact ⟨L,
      helperForCorollary_35_8_1_reflectedFirstSliceCoordinatePartial_of_packedFirstCoordinatePartial
        (K := K) (u := u) (v := v) hFinite i L hL⟩
  · intro j
    rcases hpartials (Fin.natAdd m j) with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    have hpoint :
        ∀ t : ℝ,
          directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
              (Pi.single (Fin.natAdd m j) (1 : ℝ)) t =
            directionalDifferenceQuotientAt (K u) v (Pi.single j (1 : ℝ)) t := by
      intro t
      exact
        helperForCorollary_35_8_1_packedSecondBasisQuotient_eq_secondSliceBasisQuotient
          (K := K) u v j t
    -- The second block is literally the coordinate derivative of the second slice.
    constructor
    · refine Filter.Tendsto.congr' ?_ hL.1
      exact Filter.Eventually.of_forall hpoint
    · refine Filter.Tendsto.congr' ?_ hL.2
      exact Filter.Eventually.of_forall hpoint

/-- Helper for Corollary 35.8.1: if all packed coordinate partials exist and are finite, then the
two slice subdifferentials are singletons, hence so are the saddle partial subdifferentials. -/
lemma helperForCorollary_35_8_1_singletonPartials_of_coordinatePartials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartials :
      ∀ j : Fin (m + n), ∃ L : ℝ,
        HasCoordinatePartialDerivativeAt
          (packedSaddleKernel K) (Fin.append u v) j (L : EReal)) :
    ∃ uStar : Fin m → ℝ, ∃ vStar : Fin n → ℝ,
      partialSubdifferentialInFirstVariable K u v = {uStar} ∧
        partialSubdifferentialInSecondVariable K u v = {vStar} := by
  let f : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  let g : (Fin n → ℝ) → EReal := K u
  have hf : ConvexFunction f := by
    -- The first-variable slice is treated in reflected convex form.
    simpa [f] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v
  have hg : ConvexFunction g := by
    -- The second-variable slice is convex directly from the saddle hypothesis.
    simpa [g] using hK.2 u
  have hfu : f (-u) ≠ (⊤ : EReal) ∧ f (-u) ≠ (⊥ : EReal) := by
    -- Recentering preserves finiteness of the base value.
    simpa [f] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase
        (K := K) (u := u) (v := v) hFinite
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The second slice evaluates to the original finite saddle value.
    simpa [g] using hFinite
  rcases
      helperForCorollary_35_8_1_sliceCoordinatePartials_of_packedCoordinatePartials
        (K := K) (u := u) (v := v) hFinite hpartials with
    ⟨hFirstPartials, hSecondPartials⟩
  rcases
      (convexFunction_differentiableAt_iff_directionalDerivativeHasGradient_and_coordinatePartials_imply_linearity
        f hf (-u) hfu).2 hFirstPartials with
    ⟨uStar, hFirstDir⟩
  rcases
      (convexFunction_differentiableAt_iff_directionalDerivativeHasGradient_and_coordinatePartials_imply_linearity
        g hg v hgv).2 hSecondPartials with
    ⟨vStar, hSecondDir⟩
  have hFirstTarget :
      IsSubgradientAt f (-u) (dotProductEquiv ℝ (Fin m) uStar) := by
    -- The reflected slice has directional derivative exactly `⟪uStar, ·⟫`.
    have hiff :=
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf (-u) hfu (dotProductEquiv ℝ (Fin m) uStar)).1
    apply hiff.mpr
    intro y
    simpa [hFirstDir y] using le_of_eq (hFirstDir y).symm
  have hSecondTarget :
      IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) vStar) := by
    -- The same Chapter 23 criterion applies to the second slice.
    have hiff :=
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg v hgv (dotProductEquiv ℝ (Fin n) vStar)).1
    apply hiff.mpr
    intro y
    simpa [hSecondDir y] using le_of_eq (hSecondDir y).symm
  have huniqFirst :
      ∃! w : Fin m → ℝ, IsSubgradientAt f (-u) (dotProductEquiv ℝ (Fin m) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := f) (hf := hf) (x := -u) (hx := hfu) (g := uStar) hFirstDir
  have huniqSecond :
      ∃! w : Fin n → ℝ, IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := g) (hf := hg) (x := v) (hx := hgv) (g := vStar) hSecondDir
  rcases huniqFirst with ⟨u0, _hu0, huuniq⟩
  rcases huniqSecond with ⟨v0, _hv0, hvuniq⟩
  have hu0Eq : u0 = uStar := by
    exact (huuniq uStar hFirstTarget).symm
  have hv0Eq : v0 = vStar := by
    exact (hvuniq vStar hSecondTarget).symm
  refine ⟨uStar, vStar, ?_, ?_⟩
  · ext w
    constructor
    · intro hw
      have hwMem :
          dotProductEquiv ℝ (Fin m) w ∈ subdifferentialAt f (-u) := by
        -- Transport a saddle partial into the reflected slice subdifferential.
        exact
          (helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
            (K := K) (u := u) (v := v) (uStar := w)).2 hw
      have hwSub : IsSubgradientAt f (-u) (dotProductEquiv ℝ (Fin m) w) := by
        simpa [f, subdifferentialAt] using hwMem
      have hwEq : w = u0 := huuniq w hwSub
      simpa [hu0Eq] using hwEq
    · intro hw
      have hwEq : w = uStar := by simpa using hw
      have huMem :
          dotProductEquiv ℝ (Fin m) uStar ∈ subdifferentialAt f (-u) := by
        simpa [f, subdifferentialAt] using hFirstTarget
      have huPartial :
          uStar ∈ partialSubdifferentialInFirstVariable K u v := by
        exact
          (helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
            (K := K) (u := u) (v := v) (uStar := uStar)).1
            (by simpa [f] using huMem)
      simpa [hwEq] using huPartial
  · ext w
    constructor
    · intro hw
      have hwMem :
          dotProductEquiv ℝ (Fin n) w ∈ subdifferentialAt g v := by
        -- The ordinary second-slice bridge works without any sign change.
        exact
          (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
            (K := K) (u := u) (v := v) (vStar := w)).2 hw
      have hwSub : IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) w) := by
        simpa [g, subdifferentialAt] using hwMem
      have hwEq : w = v0 := hvuniq w hwSub
      simpa [hv0Eq] using hwEq
    · intro hw
      have hwEq : w = vStar := by simpa using hw
      have hvMem :
          dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt g v := by
        simpa [g, subdifferentialAt] using hSecondTarget
      have hvPartial :
          vStar ∈ partialSubdifferentialInSecondVariable K u v := by
        exact
          (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
            (K := K) (u := u) (v := v) (vStar := vStar)).1
            (by simpa [g] using hvMem)
      simpa [hwEq] using hvPartial


/-- Differentiability of the packed extended-real map supplies the local finiteness qualification
used in the corrected form of Theorem 35.8. -/
lemma helperForCorollary_35_8_1_finiteNeighborhood_of_packedDifferentiable
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hDiff : ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) :
    SaddleKernelFiniteOnNeighborhoodAt K u v := by
  let z0 : Fin (m + n) → ℝ := Fin.append u v
  let T : Set (Fin (m + n) → ℝ) :=
    {z | z ∈ effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) (packedSaddleKernel K) ∧
      packedSaddleKernel K z ≠ (⊥ : EReal)}
  have hEvent : T ∈ nhdsWithin z0 {z | z ≠ z0} := by
    filter_upwards
      [ERealDifferentiableAt.eventually_finiteValuedWithin_punctured hDiff] with z hz
    simpa [T, z0] using hz
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hEvent with ⟨U, hU, hUT⟩
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hz0V⟩
  let e := Fin.appendHomeomorph (X := ℝ) m n
  refine ⟨e ⁻¹' V, hVopen.preimage e.continuous, ?_, ?_⟩
  · simpa [e, z0] using hz0V
  · intro p hp
    have hepV : e p ∈ V := hp
    by_cases hep : e p = z0
    · have hAt :
          packedSaddleKernel K (e p) ≠ (⊤ : EReal) ∧
            packedSaddleKernel K (e p) ≠ (⊥ : EReal) := by
        simpa [hep, z0] using ERealDifferentiableAt.finiteAt hDiff
      simpa [e, packedSaddleKernel] using hAt
    · have hepT : e p ∈ T := hUT ⟨hVU hepV, hep⟩
      have hTop : packedSaddleKernel K (e p) ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin (m + n) → ℝ)))
          (f := packedSaddleKernel K) hepT.1
      simpa [e, packedSaddleKernel] using And.intro hTop hepT.2

/-- Corollary 35.8.1, qualified extended-real form: differentiability is equivalent to local
finiteness together with a linear saddle directional derivative. The unqualified claim that
finite two-sided coordinate derivatives alone imply local finiteness is omitted: the same
off-axis `⊤/⊥` checkerboard gives a counterexample. -/
theorem section35_corollary35_8_1
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v) ↔
      SaddleKernelFiniteOnNeighborhoodAt K u v ∧
        HasLinearSaddleDirectionalDerivativeAt K u v := by
  constructor
  · intro hDiff
    have hNeighborhood :
        SaddleKernelFiniteOnNeighborhoodAt K u v :=
      helperForCorollary_35_8_1_finiteNeighborhood_of_packedDifferentiable
        (K := K) (u := u) (v := v) hDiff
    have hFiniteRect :=
      helperForCorollary_35_8_1_finiteRectangle_of_neighborhood
        (K := K) (u := u) (v := v) hNeighborhood
    rcases
        (section35_theorem35_8 (K := K) (u := u) (v := v) hK hFinite).1 hDiff with
      ⟨hGradMem, hGradUnique⟩
    have hUniqueProduct :
        ∃! g : (Fin m → ℝ) × (Fin n → ℝ), g ∈ productSubdifferentialAt K u v := by
      refine ⟨_, hGradMem, ?_⟩
      intro g hg
      exact hGradUnique g hg
    rcases
        helperForTheorem_35_8_unique_productSubgradient_gives_unique_partials
          (K := K) (u := u) (v := v) hUniqueProduct with
      ⟨uStar, vStar, hFirstSingleton, hSecondSingleton⟩
    have hLinearDir :=
      helperForTheorem_35_8_linear_saddleDirectionalDerivative_of_singleton_partials
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFinite hFiniteRect hFirstSingleton hSecondSingleton
    exact ⟨hNeighborhood, ⟨uStar, vStar, hLinearDir⟩⟩
  · rintro ⟨hNeighborhood, hLinear⟩
    have hFiniteRect :=
      helperForCorollary_35_8_1_finiteRectangle_of_neighborhood
        (K := K) (u := u) (v := v) hNeighborhood
    rcases hLinear with ⟨uStar, vStar, hDir⟩
    have hSingletons :=
      helperForCorollary_35_8_1_singletonPartials_of_linearSaddleDirectionalDerivative
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFiniteRect hDir
    exact
      helperForTheorem_35_8_packedDifferentiable_of_linear_saddleDirectionalDerivative
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFiniteRect hSingletons.1 hSingletons.2 hDir

/-- The packed real-valued map on `ℝ^(m+n)` associated to a saddle kernel `K`. -/
def packedRealSaddleKernel {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) :
    (Fin (m + n) → ℝ) → ℝ :=
  fun z => K (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))

/-- The split Fréchet-derivative vector of the packed real saddle kernel at `(u, v)`. -/
noncomputable def packedRealSaddleKernelGradientPair {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    (Fin m → ℝ) × (Fin n → ℝ) :=
  (fun i =>
    fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v) (Pi.single (Fin.castAdd n i) 1),
    fun j =>
      fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v) (Pi.single (Fin.natAdd m j) 1))

/-- Helper for Theorem 35.9: differentiability of the honest product map
`Function.uncurry K` is equivalent to differentiability of the packed map under `Fin.append`. -/
lemma helperForTheorem_35_9_uncurriedDifferentiableAt_iff_packedDifferentiableAt
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    DifferentiableAt ℝ (Function.uncurry K) (u, v) ↔
      DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append u v) := by
  let pack : ((Fin m → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin (m + n) → ℝ) :=
    { toLinearMap :=
        { toFun := fun p => Fin.append p.1 p.2
          map_add' := by
            intro p q
            ext i
            cases i using Fin.addCases <;> simp [Fin.append]
          map_smul' := by
            intro a p
            ext i
            cases i using Fin.addCases <;> simp [Fin.append] }
      cont := by
        exact (Fin.appendHomeomorph (X := ℝ) m n).continuous_toFun }
  let split : (Fin (m + n) → ℝ) →L[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toLinearMap :=
        { toFun := fun z => ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
          map_add' := by
            intro z w
            ext <;> simp
          map_smul' := by
            intro a z
            ext <;> simp }
      cont := by
        exact (Fin.appendHomeomorph (X := ℝ) m n).continuous_invFun }
  have hPackEq : packedRealSaddleKernel K ∘ pack = Function.uncurry K := by
    funext p
    rcases p with ⟨x, y⟩
    simp [pack, packedRealSaddleKernel, Function.uncurry]
  constructor
  · intro h
    -- Restrict the uncurried map along the linear splitting of packed coordinates.
    have h' : DifferentiableAt ℝ (Function.uncurry K) (split (Fin.append u v)) := by
      simpa [split] using h
    have hcomp : DifferentiableAt ℝ ((Function.uncurry K) ∘ split) (Fin.append u v) :=
      h'.comp (Fin.append u v) split.differentiableAt
    simpa [split, packedRealSaddleKernel, Function.comp, Function.uncurry] using hcomp
  · intro h
    -- Conversely, compose the packed map with the linear packing map `(u, v) ↦ Fin.append u v`.
    have hcomp : DifferentiableAt ℝ (packedRealSaddleKernel K ∘ pack) (u, v) :=
      h.comp (u, v) pack.differentiableAt
    simpa [hPackEq] using hcomp

/-- Helper for Theorem 35.9: on a ball whose doubled closed ball stays inside `C × D`, the
exceptional set where the packed map fails to be differentiable has measure zero. -/
lemma helperForTheorem_35_9_nullExceptionalSet_onBall
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (c : (Fin m → ℝ) × (Fin n → ℝ)) {r : ℝ} (hr : 0 < r)
    (hclosedSub : Metric.closedBall c (2 * r) ⊆ C ×ˢ D) :
    MeasureTheory.volume
        (Metric.ball c r \
          {p | p ∈ C ×ˢ D ∧
            DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append p.1 p.2)}) = 0 := by
  let S : Set ((Fin m → ℝ) × (Fin n → ℝ)) := Metric.closedBall c (2 * r)
  have hSsub : S ⊆ C ×ˢ D := by
    simpa [S] using hclosedSub
  haveI :
      MeasureTheory.Measure.IsAddHaarMeasure
        (MeasureTheory.volume :
          MeasureTheory.Measure ((Fin m → ℝ) × (Fin n → ℝ))) := by
    change
      MeasureTheory.Measure.IsAddHaarMeasure
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
    infer_instance
  let I : Type := PUnit
  let Kfam : I → (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun _ => K
  have hCrel :=
    helperForTheorem_35_7_isRelativelyOpenConvex_of_isOpen (hsConv := hC_conv) (hsOpen := hC_open)
  have hDrel :=
    helperForTheorem_35_7_isRelativelyOpenConvex_of_isOpen (hsConv := hD_conv) (hsOpen := hD_open)
  have hKfam : ∀ i : I, IsRealConcaveConvexOn C D (Kfam i) := by
    intro i
    cases i
    simpa [Kfam] using hK
  have hWitness :
      ∃ C' : Set (Fin m → ℝ),
        ∃ D' : Set (Fin n → ℝ),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ×ˢ D ⊆ convexHull ℝ (closure (C' ×ˢ D')) ∧
          Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (Kfam i)) (C' ×ˢ D') := by
    refine ⟨C, D, Set.Subset.rfl, Set.Subset.rfl, ?_, ?_⟩
    · intro p hp
      exact (subset_convexHull ℝ (closure (C ×ˢ D))) (subset_closure hp)
    · intro p hp
      rcases p with ⟨x, y⟩
      simpa [I, Kfam, Function.uncurry, Set.range_const] using
        (Bornology.isBounded_singleton (s := ({K x y} : Set ℝ)))
  rcases
      helperForTheorem_35_7_section35_theorem35_2_on_pi
        (I := I) (m := m) (n := n) (C := C) (D := D) (K := Kfam)
        hCrel hDrel hKfam hWitness S hSsub Metric.isClosed_closedBall
        (isCompact_closedBall c (2 * r)).isBounded with
    ⟨_hUbdd, hEqui⟩
  rcases hEqui with ⟨L, hL⟩
  have hLip : LipschitzOnWith L (Function.uncurry K) S := by
    simpa [I, Kfam, Function.uncurry] using hL PUnit.unit
  have hAErestrict :
      ∀ᵐ p ∂(MeasureTheory.volume.restrict S), DifferentiableWithinAt ℝ (Function.uncurry K) S p :=
    hLip.ae_differentiableWithinAt (hs := Metric.isClosed_closedBall.measurableSet)
  have hAE :
      ∀ᵐ p ∂(MeasureTheory.volume :
        MeasureTheory.Measure ((Fin m → ℝ) × (Fin n → ℝ))),
        p ∈ S → DifferentiableWithinAt ℝ (Function.uncurry K) S p :=
    (MeasureTheory.ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).1 hAErestrict
  let badS : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
    {p | p ∈ S ∧ ¬ DifferentiableWithinAt ℝ (Function.uncurry K) S p}
  have hBadNull : MeasureTheory.volume badS = 0 := by
    have hBadCompl :
        ∀ᵐ p ∂(MeasureTheory.volume :
          MeasureTheory.Measure ((Fin m → ℝ) × (Fin n → ℝ))), p ∉ badS := by
      simpa [badS] using hAE
    exact (MeasureTheory.compl_mem_ae_iff).mp hBadCompl
  have hsubsetBad :
      Metric.ball c r \
          {p | p ∈ C ×ˢ D ∧
            DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append p.1 p.2)} ⊆
        badS := by
    intro p hp
    constructor
    · have hpdist : dist p c < r := hp.1
      have : dist p c ≤ 2 * r := by
        linarith
      simpa [S] using this
    · by_contra hpDiff
      have hSNhds : S ∈ 𝓝 p := by
        have hpdist : dist p c < 2 * r := by
          have hpdist' : dist p c < r := hp.1
          linarith
        exact Metric.closedBall_mem_nhds_of_mem (by simpa [Metric.mem_ball] using hpdist)
      have hpS : p ∈ S := by
        have hpdist : dist p c < r := hp.1
        have : dist p c ≤ 2 * r := by
          linarith
        simpa [S] using this
      have hpDiffAt : DifferentiableAt ℝ (Function.uncurry K) p :=
        hpDiff.differentiableAt hSNhds
      have hpPacked :
          DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append p.1 p.2) :=
        (helperForTheorem_35_9_uncurriedDifferentiableAt_iff_packedDifferentiableAt
          (K := K) (u := p.1) (v := p.2)).1 hpDiffAt
      exact hp.2 ⟨hSsub hpS, hpPacked⟩
  exact MeasureTheory.measure_mono_null hsubsetBad hBadNull

/-- Helper for Theorem 35.9: at a packed differentiability point in `C × D`, the real saddle
subdifferential is the singleton determined by the split packed gradient. -/
lemma helperForTheorem_35_9_realSaddleSubdifferential_eq_singleton_of_mem_E
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (hdiff : DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append u v)) :
    realSaddleSubdifferentialOn C D K u v = {packedRealSaddleKernelGradientPair K u v} := by
  classical
  let grad : (Fin m → ℝ) × (Fin n → ℝ) := packedRealSaddleKernelGradientPair K u v
  let appendFirstLinear : (Fin m → ℝ) →L[ℝ] (Fin (m + n) → ℝ) := by
    let L : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
      { toFun := fun x => Fin.append x (0 : Fin n → ℝ)
        map_add' := by
          intro x1 x2
          ext i
          cases i using Fin.addCases <;> simp [Fin.append]
        map_smul' := by
          intro a x
          ext i
          cases i using Fin.addCases <;> simp [Fin.append] }
    exact ⟨L, L.continuous_of_finiteDimensional⟩
  let appendSecondLinear : (Fin n → ℝ) →L[ℝ] (Fin (m + n) → ℝ) := by
    let L : (Fin n → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
      { toFun := fun y => Fin.append (0 : Fin m → ℝ) y
        map_add' := by
          intro y1 y2
          ext i
          cases i using Fin.addCases <;> simp [Fin.append]
        map_smul' := by
          intro a y
          ext i
          cases i using Fin.addCases <;> simp [Fin.append] }
    exact ⟨L, L.continuous_of_finiteDimensional⟩
  let f : (Fin m → ℝ) → ℝ := fun x => -(K x v)
  let g : (Fin n → ℝ) → ℝ := fun y => K u y
  let fExt : (Fin m → ℝ) → EReal :=
    fun x => ((f x : ℝ) : EReal) + indicatorFunction C x
  let gExt : (Fin n → ℝ) → EReal :=
    fun y => ((g y : ℝ) : EReal) + indicatorFunction D y
  have hfExtEqIte :
      fExt = (fun x : Fin m → ℝ => if x ∈ C then ((f x : ℝ) : EReal) else (⊤ : EReal)) := by
    funext x
    by_cases hx : x ∈ C <;> simp [fExt, indicatorFunction, hx]
  have hgExtEqIte :
      gExt = (fun y : Fin n → ℝ => if y ∈ D then ((g y : ℝ) : EReal) else (⊤ : EReal)) := by
    funext y
    by_cases hy : y ∈ D <;> simp [gExt, indicatorFunction, hy]
  -- Differentiate the two honest slices by restricting the packed real map along affine
  -- first-block and second-block embeddings.
  have hAppendFirst :
      HasFDerivAt (fun x : Fin m → ℝ => Fin.append x v) appendFirstLinear u := by
    have hbase :
        HasFDerivAt (fun x : Fin m → ℝ => Fin.append x (0 : Fin n → ℝ))
          appendFirstLinear u := by
      simpa [appendFirstLinear] using appendFirstLinear.hasFDerivAt
    have hconst :
        HasFDerivAt
          (fun x : Fin m → ℝ => Fin.append (0 : Fin m → ℝ) v + Fin.append x (0 : Fin n → ℝ))
          appendFirstLinear u := by
      simpa using hbase.const_add (Fin.append (0 : Fin m → ℝ) v)
    refine hconst.congr_of_eventuallyEq ?_
    filter_upwards with x
    ext i
    cases i using Fin.addCases <;> simp [Fin.append]
  have hAppendSecond :
      HasFDerivAt (fun y : Fin n → ℝ => Fin.append u y) appendSecondLinear v := by
    have hbase :
        HasFDerivAt (fun y : Fin n → ℝ => Fin.append (0 : Fin m → ℝ) y)
          appendSecondLinear v := by
      simpa [appendSecondLinear] using appendSecondLinear.hasFDerivAt
    have hconst :
        HasFDerivAt
          (fun y : Fin n → ℝ => Fin.append u (0 : Fin n → ℝ) + Fin.append (0 : Fin m → ℝ) y)
          appendSecondLinear v := by
      simpa using hbase.const_add (Fin.append u (0 : Fin n → ℝ))
    refine hconst.congr_of_eventuallyEq ?_
    filter_upwards with y
    ext i
    cases i using Fin.addCases <;> simp [Fin.append]
  have hPackedFirstDiff :
      DifferentiableAt ℝ (fun x : Fin m → ℝ => K x v) u := by
    have hcomp :
        HasFDerivAt (fun x : Fin m → ℝ => packedRealSaddleKernel K (Fin.append x v))
          ((fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)).comp appendFirstLinear) u := by
      exact hdiff.hasFDerivAt.comp u hAppendFirst
    simpa [packedRealSaddleKernel] using hcomp.differentiableAt
  have hPackedSecondDiff :
      DifferentiableAt ℝ (fun y : Fin n → ℝ => K u y) v := by
    have hcomp :
        HasFDerivAt (fun y : Fin n → ℝ => packedRealSaddleKernel K (Fin.append u y))
          ((fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)).comp appendSecondLinear) v := by
      exact hdiff.hasFDerivAt.comp v hAppendSecond
    simpa [packedRealSaddleKernel] using hcomp.differentiableAt
  have hfDiff : DifferentiableAt ℝ f u := by
    simpa [f] using hPackedFirstDiff.neg
  have hgDiff : DifferentiableAt ℝ g v := by
    simpa [g] using hPackedSecondDiff
  -- Apply the Chapter 25 `+∞`-extension theorem to the two convex slices on `C` and `D`.
  have hfConvOn : ConvexOn ℝ C f := (hK.1 v hv).neg
  have hgConvOn : ConvexOn ℝ D g := hK.2 u hu
  have hfExtData :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := C) (f := f) hfConvOn
  have hgExtData :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := D) (f := g) hgConvOn
  have hfExtConv : ConvexFunction fExt := by
    rw [hfExtEqIte]
    simpa using hfExtData.1
  have hgExtConv : ConvexFunction gExt := by
    rw [hgExtEqIte]
    simpa using hgExtData.1
  have hfuExt : fExt u ≠ (⊤ : EReal) ∧ fExt u ≠ (⊥ : EReal) := by
    rw [hfExtEqIte]
    simpa using hfExtData.2 u hu
  have hgvExt : gExt v ≠ (⊤ : EReal) ∧ gExt v ≠ (⊥ : EReal) := by
    rw [hgExtEqIte]
    simpa using hgExtData.2 v hv
  rcases
      helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := hC_open) (f := f) (x := u) hu hfDiff with
    ⟨hfExtDiff, hfExtGradEq⟩
  rcases
      helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := hD_open) (f := g) (x := v) hv hgDiff with
    ⟨hgExtDiff, hgExtGradEq⟩
  -- Identify the extension gradients with the split packed Fréchet derivative coordinates.
  have hFirstGradCoord :
      ∀ i : Fin m,
        euclideanGradientAt f u i =
          -fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
            (Pi.single (Fin.castAdd n i) (1 : ℝ)) := by
    intro i
    have hlineSlice :
        HasDerivAt
          (fun t : ℝ => f (u + t • (Pi.single i (1 : ℝ) : Fin m → ℝ)))
          ((euclideanGradientAt f u) i) 0 := by
      have hdir :=
        directionalDerivative_eq_dot_euclideanGradient_of_differentiableAt
          (f := f) (x := u) (y := (Pi.single i (1 : ℝ) : Fin m → ℝ)) hfDiff
      simpa [dotProduct, Pi.single_apply] using hdir
    have hlinePacked :
        HasDerivAt
          (fun t : ℝ => f (u + t • (Pi.single i (1 : ℝ) : Fin m → ℝ)))
          (-fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
            ((Pi.single (Fin.castAdd n i) (1 : ℝ)) : Fin (m + n) → ℝ)) 0 := by
      have hraw :
          HasDerivAt
            (fun t : ℝ =>
              packedRealSaddleKernel K
                (Fin.append u v +
                  t • ((Pi.single (Fin.castAdd n i) (1 : ℝ)) : Fin (m + n) → ℝ)))
            (fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
              ((Pi.single (Fin.castAdd n i) (1 : ℝ)) : Fin (m + n) → ℝ)) 0 := by
        simpa [HasLineDerivAt] using
          hdiff.hasFDerivAt.hasLineDerivAt
            (((Pi.single (Fin.castAdd n i) (1 : ℝ)) : Fin (m + n) → ℝ))
      have hfun :
          (fun t : ℝ =>
            packedRealSaddleKernel K
              (Fin.append u v +
                t • ((Pi.single (Fin.castAdd n i) (1 : ℝ)) : Fin (m + n) → ℝ))) =
            (fun t : ℝ => K (u + t • (Pi.single i (1 : ℝ) : Fin m → ℝ)) v) := by
        funext t
        have hfirst :
            (fun i' : Fin m =>
              (Fin.append u v +
                  t • ((Pi.single (Fin.castAdd n i) (1 : ℝ)) : Fin (m + n) → ℝ))
                (Fin.castAdd n i')) =
              (u + t • (Pi.single i (1 : ℝ) : Fin m → ℝ)) := by
          funext i'
          by_cases hEq : i' = i
          · subst hEq
            simp [Pi.add_apply, Pi.smul_apply, Fin.append]
          · have hne : Fin.castAdd n i' ≠ Fin.castAdd n i := by
              intro h
              apply hEq
              ext
              simpa [Fin.castAdd] using congrArg Fin.val h
            simp [Pi.add_apply, Pi.smul_apply, Fin.append, Pi.single_apply, hEq, hne]
        have hsecond :
            (fun j : Fin n =>
              (Fin.append u v +
                  t • ((Pi.single (Fin.castAdd n i) (1 : ℝ)) : Fin (m + n) → ℝ))
                (Fin.natAdd m j)) = v := by
          funext j
          have hne : Fin.natAdd m j ≠ Fin.castAdd n i := by
            intro h
            have hval := congrArg Fin.val h
            simp [Fin.natAdd, Fin.castAdd] at hval
            omega
          simp [Pi.add_apply, Pi.smul_apply, Fin.append, Pi.single_apply, hne]
        rw [packedRealSaddleKernel, hfirst, hsecond]
      rw [hfun] at hraw
      simpa [f] using hraw.neg
    exact hlineSlice.unique hlinePacked
  have hSecondGradCoord :
      ∀ j : Fin n,
        euclideanGradientAt g v j =
          fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
            (Pi.single (Fin.natAdd m j) (1 : ℝ)) := by
    intro j
    have hlineSlice :
        HasDerivAt
          (fun t : ℝ => g (v + t • (Pi.single j (1 : ℝ) : Fin n → ℝ)))
          ((euclideanGradientAt g v) j) 0 := by
      have hdir :=
        directionalDerivative_eq_dot_euclideanGradient_of_differentiableAt
          (f := g) (x := v) (y := (Pi.single j (1 : ℝ) : Fin n → ℝ)) hgDiff
      simpa [dotProduct, Pi.single_apply] using hdir
    have hlinePacked :
        HasDerivAt
          (fun t : ℝ => g (v + t • (Pi.single j (1 : ℝ) : Fin n → ℝ)))
          (fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
            ((Pi.single (Fin.natAdd m j) (1 : ℝ)) : Fin (m + n) → ℝ)) 0 := by
      have hraw :
          HasDerivAt
            (fun t : ℝ =>
              packedRealSaddleKernel K
                (Fin.append u v +
                  t • ((Pi.single (Fin.natAdd m j) (1 : ℝ)) : Fin (m + n) → ℝ)))
            (fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
              ((Pi.single (Fin.natAdd m j) (1 : ℝ)) : Fin (m + n) → ℝ)) 0 := by
        simpa [HasLineDerivAt] using
          hdiff.hasFDerivAt.hasLineDerivAt
            (((Pi.single (Fin.natAdd m j) (1 : ℝ)) : Fin (m + n) → ℝ))
      have hfun :
          (fun t : ℝ =>
            packedRealSaddleKernel K
              (Fin.append u v +
                t • ((Pi.single (Fin.natAdd m j) (1 : ℝ)) : Fin (m + n) → ℝ))) =
            (fun t : ℝ => K u (v + t • (Pi.single j (1 : ℝ) : Fin n → ℝ))) := by
        funext t
        have hfirst :
            (fun i : Fin m =>
              (Fin.append u v +
                  t • ((Pi.single (Fin.natAdd m j) (1 : ℝ)) : Fin (m + n) → ℝ))
                (Fin.castAdd n i)) = u := by
          funext i
          have hne : Fin.castAdd n i ≠ Fin.natAdd m j := by
            intro h
            have hval := congrArg Fin.val h
            simp [Fin.natAdd, Fin.castAdd] at hval
            omega
          simp [Pi.add_apply, Pi.smul_apply, Fin.append, Pi.single_apply, hne]
        have hsecond :
            (fun j' : Fin n =>
              (Fin.append u v +
                  t • ((Pi.single (Fin.natAdd m j) (1 : ℝ)) : Fin (m + n) → ℝ))
                (Fin.natAdd m j')) =
              (v + t • (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
          funext j'
          by_cases hEq : j' = j
          · subst hEq
            simp [Pi.add_apply, Pi.smul_apply, Fin.append, Pi.single_apply]
          · have hne : Fin.natAdd m j' ≠ Fin.natAdd m j := by
              intro h
              apply hEq
              ext
              simpa [Fin.natAdd] using congrArg Fin.val h
            simp [Pi.add_apply, Pi.smul_apply, Fin.append, Pi.single_apply, hEq, hne]
        rw [packedRealSaddleKernel, hfirst, hsecond]
      rw [hfun] at hraw
      simpa [g] using hraw
    exact hlineSlice.unique hlinePacked
  have hFirstGradEq : erealGradientAt hfExtDiff = -grad.1 := by
    ext i
    calc
      erealGradientAt hfExtDiff i = euclideanGradientAt f u i := by
        simpa [hfExtGradEq]
      _ =
          -fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
            (Pi.single (Fin.castAdd n i) (1 : ℝ)) := hFirstGradCoord i
      _ = (-grad.1) i := by
            simp [grad, packedRealSaddleKernelGradientPair]
  have hSecondGradEq : erealGradientAt hgExtDiff = grad.2 := by
    ext j
    calc
      erealGradientAt hgExtDiff j = euclideanGradientAt g v j := by
        simpa [hgExtGradEq]
      _ =
          fderiv ℝ (packedRealSaddleKernel K) (Fin.append u v)
            (Pi.single (Fin.natAdd m j) (1 : ℝ)) := hSecondGradCoord j
      _ = grad.2 j := by
            simp [grad, packedRealSaddleKernelGradientPair]
  -- The convex slice extensions therefore have unique subgradients given by the packed gradient.
  have hfSubData :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      fExt hfExtConv u hfuExt).1 hfExtDiff
  have hgSubData :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      gExt hgExtConv v hgvExt).1 hgExtDiff
  have hFirstTarget :
      IsSubgradientAt fExt u (dotProductEquiv ℝ (Fin m) (-grad.1)) := by
    simpa [hFirstGradEq] using hfSubData.1
  have hSecondTarget :
      IsSubgradientAt gExt v (dotProductEquiv ℝ (Fin n) grad.2) := by
    simpa [hSecondGradEq] using hgSubData.1
  have hFirstUnique :
      ∀ w : Fin m → ℝ,
        IsSubgradientAt fExt u (dotProductEquiv ℝ (Fin m) w) → w = -grad.1 := by
    intro w hw
    calc
      w = erealGradientAt hfExtDiff := hfSubData.2.2 w hw
      _ = -grad.1 := hFirstGradEq
  have hSecondUnique :
      ∀ w : Fin n → ℝ,
        IsSubgradientAt gExt v (dotProductEquiv ℝ (Fin n) w) → w = grad.2 := by
    intro w hw
    calc
      w = erealGradientAt hgExtDiff := hgSubData.2.2 w hw
      _ = grad.2 := hSecondGradEq
  -- Translate the one-variable singleton facts back into the real saddle partial subdifferentials.
  have hBridge :
      (∀ uStar : Fin m → ℝ,
          uStar ∈ realPartialSubdifferentialInFirstVariableOn C K u v ↔
            dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt fExt u) ∧
        (∀ vStar : Fin n → ℝ,
          vStar ∈ realPartialSubdifferentialInSecondVariableOn D K u v ↔
            dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt gExt v) := by
    simpa [f, g, hfExtEqIte, hgExtEqIte] using
      helperForTheorem_35_7_realPartialSubdifferential_bridges
        (C := C) (D := D) (K := K) (u := u) (v := v) hu hv
  have hFirstSingleton :
      realPartialSubdifferentialInFirstVariableOn C K u v = {grad.1} := by
    ext w
    constructor
    · intro hw
      have hwSub : IsSubgradientAt fExt u (dotProductEquiv ℝ (Fin m) (-w)) := by
        have hwMem :
            dotProductEquiv ℝ (Fin m) (-w) ∈ subdifferentialAt fExt u := (hBridge.1 w).1 hw
        simpa [subdifferentialAt] using hwMem
      have hEqNeg : -w = -grad.1 := hFirstUnique (-w) hwSub
      have hEq : w = grad.1 := by
        simpa using congrArg Neg.neg hEqNeg
      simpa [hEq]
    · intro hw
      have hwEq : w = grad.1 := by simpa using hw
      have hMemSub : dotProductEquiv ℝ (Fin m) (-grad.1) ∈ subdifferentialAt fExt u := by
        simpa [subdifferentialAt] using hFirstTarget
      have hMem :
          grad.1 ∈ realPartialSubdifferentialInFirstVariableOn C K u v := by
        exact (hBridge.1 grad.1).2 hMemSub
      simpa [hwEq] using hMem
  have hSecondSingleton :
      realPartialSubdifferentialInSecondVariableOn D K u v = {grad.2} := by
    ext w
    constructor
    · intro hw
      have hwSub : IsSubgradientAt gExt v (dotProductEquiv ℝ (Fin n) w) := by
        have hwMem :
            dotProductEquiv ℝ (Fin n) w ∈ subdifferentialAt gExt v := (hBridge.2 w).1 hw
        simpa [subdifferentialAt] using hwMem
      have hEq : w = grad.2 := hSecondUnique w hwSub
      simpa [hEq]
    · intro hw
      have hwEq : w = grad.2 := by simpa using hw
      have hMemSub : dotProductEquiv ℝ (Fin n) grad.2 ∈ subdifferentialAt gExt v := by
        simpa [subdifferentialAt] using hSecondTarget
      have hMem :
          grad.2 ∈ realPartialSubdifferentialInSecondVariableOn D K u v := by
        exact (hBridge.2 grad.2).2 hMemSub
      simpa [hwEq] using hMem
  -- The saddle subdifferential is the product of the two singleton partial subdifferentials.
  ext p
  constructor
  · intro hp
    have hpParts :
        p.1 ∈ realPartialSubdifferentialInFirstVariableOn C K u v ∧
          p.2 ∈ realPartialSubdifferentialInSecondVariableOn D K u v := by
      simpa [realSaddleSubdifferentialOn] using hp
    have hp1 : p.1 = grad.1 := by
      simpa [hFirstSingleton] using hpParts.1
    have hp2 : p.2 = grad.2 := by
      simpa [hSecondSingleton] using hpParts.2
    exact Prod.ext hp1 hp2
  · intro hp
    rcases hp with rfl
    have hFirstMem : grad.1 ∈ realPartialSubdifferentialInFirstVariableOn C K u v := by
      simpa [hFirstSingleton]
    have hSecondMem : grad.2 ∈ realPartialSubdifferentialInSecondVariableOn D K u v := by
      simpa [hSecondSingleton]
    simpa [realSaddleSubdifferentialOn] using And.intro hFirstMem hSecondMem

end Section35
end Chap07
