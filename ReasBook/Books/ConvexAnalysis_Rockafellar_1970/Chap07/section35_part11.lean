/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part10

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

-- Proof sketch: view `K` as the proper `EReal`-valued function on `ℝ^m × ℝ^n` given by
-- `Function.uncurry K`. An interior point of `dom K` has an open product neighborhood contained in
-- that domain, and projecting this neighborhood to the first and second coordinates yields open
-- neighborhoods proving that `u` and `v` lie in the interiors of the corresponding slice domains.
/-- Helper for Text 35.6.8: an interior point of the product effective domain admits an open
rectangle neighborhood contained in that domain. -/
lemma helperForText_35_6_8_openRectangleInsideProductDomain
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (erealDom (Function.uncurry K))) :
    ∃ U : Set (Fin m → ℝ), ∃ V : Set (Fin n → ℝ),
      IsOpen U ∧ u ∈ U ∧ IsOpen V ∧ v ∈ V ∧
        Set.prod U V ⊆ erealDom (Function.uncurry K) := by
  have hNhds : erealDom (Function.uncurry K) ∈ nhds (u, v) :=
    mem_interior_iff_mem_nhds.1 hInterior
  -- Split the product neighborhood into coordinate neighborhoods.
  rcases (mem_nhds_prod_iff).1 hNhds with ⟨U₀, hU₀, V₀, hV₀, hUV₀⟩
  -- Replace each neighborhood by an open set through the base point.
  rcases mem_nhds_iff.1 hU₀ with ⟨U, hUsub, hUopen, huU⟩
  rcases mem_nhds_iff.1 hV₀ with ⟨V, hVsub, hVopen, hvV⟩
  refine ⟨U, V, hUopen, huU, hVopen, hvV, ?_⟩
  -- The smaller open rectangle still stays inside the effective domain.
  intro p hp
  exact hUV₀ ⟨hUsub hp.1, hVsub hp.2⟩

/-- Helper for Text 35.6.8: a rectangle inside `dom K` gives a first-coordinate open witness for
the fixed-second-coordinate slice domain. -/
lemma helperForText_35_6_8_firstSliceDomain_of_rectangle
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {v : Fin n → ℝ}
    {U : Set (Fin m → ℝ)} {V : Set (Fin n → ℝ)}
    (hRect : Set.prod U V ⊆ erealDom (Function.uncurry K))
    (hv : v ∈ V) :
    U ⊆ erealDom (fun u' : Fin m → ℝ => K u' v) := by
  intro u' hu'
  -- Fix the second coordinate at `v` and read the pair `(u', v)` inside the rectangle.
  have hPair : (u', v) ∈ Set.prod U V := ⟨hu', hv⟩
  simpa [erealDom, Function.uncurry] using hRect hPair

/-- Helper for Text 35.6.8: a rectangle inside `dom K` gives a second-coordinate open witness for
the fixed-first-coordinate slice domain. -/
lemma helperForText_35_6_8_secondSliceDomain_of_rectangle
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ}
    {U : Set (Fin m → ℝ)} {V : Set (Fin n → ℝ)}
    (hRect : Set.prod U V ⊆ erealDom (Function.uncurry K))
    (hu : u ∈ U) :
    V ⊆ erealDom (fun v' : Fin n → ℝ => K u v') := by
  intro v' hv'
  -- Fix the first coordinate at `u` and read the pair `(u, v')` inside the rectangle.
  have hPair : (u, v') ∈ Set.prod U V := ⟨hu, hv'⟩
  simpa [erealDom, Function.uncurry] using hRect hPair

/-- Text 35.6.8: assume `K` is proper and `(u, v)` lies in the interior of `dom K`. Then
`u ∈ interior (dom K(·, v))` and `v ∈ interior (dom K(u, ·))`, where these interiors are taken
in the Euclidean topologies of `ℝ^m` and `ℝ^n`, respectively. -/
theorem section35_text35_6_8
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hProper : ProperERealFunction (Function.uncurry K))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (erealDom (Function.uncurry K))) :
    u ∈ interior (erealDom fun u' : Fin m → ℝ => K u' v) ∧
      v ∈ interior (erealDom fun v' : Fin n → ℝ => K u v') := by
  let _ := hProper
  rcases helperForText_35_6_8_openRectangleInsideProductDomain
      (K := K) (u := u) (v := v) hInterior with
    ⟨U, V, hUopen, huU, hVopen, hvV, hRect⟩
  constructor
  · -- The first coordinate of the open rectangle witnesses interiority of the first slice domain.
    refine mem_interior_iff_mem_nhds.2 ?_
    refine Filter.mem_of_superset (hUopen.mem_nhds huU) ?_
    exact helperForText_35_6_8_firstSliceDomain_of_rectangle
      (K := K) (v := v) hRect hvV
  · -- The second coordinate of the same rectangle witnesses interiority of the second slice.
    refine mem_interior_iff_mem_nhds.2 ?_
    refine Filter.mem_of_superset (hVopen.mem_nhds hvV) ?_
    exact helperForText_35_6_8_secondSliceDomain_of_rectangle
      (K := K) (u := u) hRect huU

/-- Helper for Text 35.6.9: properness rules out `⊥` everywhere, so the reflected first slice
`x ↦ -K (-x) v` has full effective domain. In particular, `-u` is an interior point of that
effective domain. -/
lemma helperForText_35_6_9_reflectedFirstSlice_mem_interior_effectiveDomain
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hProper : ProperERealFunction (Function.uncurry K))
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    -u ∈ interior
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun x : Fin m → ℝ => -K (-x) v)) := by
  have hDom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun x : Fin m → ℝ => -K (-x) v) =
        Set.univ := by
    ext x
    -- Properness excludes `K (-x) v = ⊥`, so the reflected slice is always strictly below `⊤`.
    constructor
    · intro _hx
      simp
    · intro _hx
      simp [effectiveDomain_eq, lt_top_iff_ne_top]
      exact hProper.1 (-x, v)
  -- Once the effective domain is all of `ℝ^m`, its interior is also all of `ℝ^m`.
  rw [hDom]
  simp

/-- Helper for Text 35.6.9: the first partial subdifferential is nonempty, closed, bounded, and
convex once `(u, v)` lies in the interior of `dom K`. -/
lemma helperForText_35_6_9_firstPartial_nonempty_closed_bounded_convex
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    (hProper : ProperERealFunction (Function.uncurry K))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (erealDom (Function.uncurry K))) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
      IsClosed (partialSubdifferentialInFirstVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) ∧
      Convex ℝ (partialSubdifferentialInFirstVariable K u v) := by
  let g : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  have hKuv_top : K u v ≠ (⊤ : EReal) := by
    have hmem : (u, v) ∈ erealDom (Function.uncurry K) := interior_subset hInterior
    -- Interior points of `dom K` are finite below `⊤`.
    simpa [erealDom, Function.uncurry, lt_top_iff_ne_top] using hmem
  have hKuv_finite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := by
    exact ⟨hKuv_top, hProper.1 (u, v)⟩
  have hg : ConvexFunction g := by
    -- The reflected first slice is convex by the first saddle branch.
    simpa [g] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hSaddle v
  have hgu : g (-u) ≠ (⊤ : EReal) ∧ g (-u) ≠ (⊥ : EReal) := by
    -- The reflected base value is just `-K u v`, so finiteness transports across negation.
    simpa [g] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase
        (K := K) (u := u) (v := v) hKuv_finite
  have hBaseInterior :
      -u ∈ interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
    -- Properness makes the reflected slice finite below `⊤` everywhere.
    simpa [g] using
      helperForText_35_6_9_reflectedFirstSlice_mem_interior_effectiveDomain
        (K := K) hProper u v
  have hgProper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g :=
    helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
      hg hBaseInterior hgu.2
  have h23 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      g hgProper (-u)
  have hSubNonemptyBounded :
      Set.Nonempty (subdifferentialAt g (-u)) ∧
        Bornology.IsBounded
          (((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt g (-u))) :=
    (h23.2.2.1).2 hBaseInterior
  have hSliceClosed :
      IsClosed (((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt g (-u))) := by
    -- The Chapter 23 closedness theorem applies at the finite base point of the reflected slice.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg (-u) hgu (0 : Module.Dual ℝ (Fin m → ℝ))).2.1
  have hSliceConvex :
      Convex ℝ (((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt g (-u))) := by
    -- The same theorem also gives convexity of the vectorized slice subdifferential.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg (-u) hgu (0 : Module.Dual ℝ (Fin m → ℝ))).2.2.1
  have hPartialNonempty :
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) :=
    (helperForText_35_6_6_partialFirst_nonempty_iff_sliceSubdifferential_nonempty
      (K := K) (u := u) (v := v)).2 hSubNonemptyBounded.1
  have hFirstEq :
      ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt g (-u)) =
        partialSubdifferentialInFirstVariable K u v := by
    -- This is the reflected-slice identification from Text 35.6.6 in the present notation.
    simpa [g] using
      helperForText_35_6_6_partialFirst_eq_sliceSubdifferential
        (K := K) (u := u) (v := v)
  have hPartialClosed :
      IsClosed (partialSubdifferentialInFirstVariable K u v) := by
    -- The reflected slice subdifferential is exactly the textbook first partial subdifferential.
    simpa [hFirstEq] using hSliceClosed
  have hPartialBounded :
      Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) := by
    -- The boundedness statement transports through the same slice identification.
    simpa [hFirstEq] using hSubNonemptyBounded.2
  have hPartialConvex :
      Convex ℝ (partialSubdifferentialInFirstVariable K u v) := by
    -- Convexity is likewise inherited from the reflected slice subdifferential.
    simpa [hFirstEq] using hSliceConvex
  exact ⟨hPartialNonempty, hPartialClosed, hPartialBounded, hPartialConvex⟩

/-- Helper for Text 35.6.9: the second partial subdifferential is nonempty, closed, bounded, and
convex once `(u, v)` lies in the interior of `dom K`. -/
lemma helperForText_35_6_9_secondPartial_nonempty_closed_bounded_convex
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    (hProper : ProperERealFunction (Function.uncurry K))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (erealDom (Function.uncurry K))) :
    Set.Nonempty (partialSubdifferentialInSecondVariable K u v) ∧
      IsClosed (partialSubdifferentialInSecondVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v) ∧
      Convex ℝ (partialSubdifferentialInSecondVariable K u v) := by
  let g : (Fin n → ℝ) → EReal := K u
  have hSlicesInterior := section35_text35_6_8 (K := K) hProper hInterior
  have hvInt :
      v ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
    -- For the honest second slice, `dom` is exactly the usual effective domain.
    simpa [g, erealDom, effectiveDomain_eq] using hSlicesInterior.2
  have hKuv_top : K u v ≠ (⊤ : EReal) := by
    have hmem : (u, v) ∈ erealDom (Function.uncurry K) := interior_subset hInterior
    -- Interior points of `dom K` are finite below `⊤`.
    simpa [erealDom, Function.uncurry, lt_top_iff_ne_top] using hmem
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The slice base value is the same finite kernel value `K u v`.
    simpa [g] using And.intro hKuv_top (hProper.1 (u, v))
  have hg : ConvexFunction g := by
    -- Fixing the first variable leaves the second slice convex.
    simpa [g] using hSaddle.2 u
  have hgProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
      hg hvInt hgv.2
  have h23 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      g hgProper v
  have hSubNonemptyBounded :
      Set.Nonempty (subdifferentialAt g v) ∧
        Bornology.IsBounded
          (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v)) :=
    (h23.2.2.1).2 hvInt
  have hSliceClosed :
      IsClosed (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v)) := by
    -- The Chapter 23 closedness theorem applies at the finite base point of the second slice.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg v hgv (0 : Module.Dual ℝ (Fin n → ℝ))).2.1
  have hSliceConvex :
      Convex ℝ (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v)) := by
    -- The same theorem also gives convexity of the vectorized slice subdifferential.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg v hgv (0 : Module.Dual ℝ (Fin n → ℝ))).2.2.1
  have hPartialNonempty :
      Set.Nonempty (partialSubdifferentialInSecondVariable K u v) :=
    (helperForText_35_6_7_partialSecond_nonempty_iff_sliceSubdifferential_nonempty
      (K := K) (u := u) (v := v)).2 hSubNonemptyBounded.1
  have hSecondEq :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v) =
        partialSubdifferentialInSecondVariable K u v := by
    -- This is the direct slice identification from Text 35.6.7 in the present notation.
    simpa [g] using
      helperForText_35_6_7_partialSecond_eq_sliceSubdifferential
        (K := K) (u := u) (v := v)
  have hPartialClosed :
      IsClosed (partialSubdifferentialInSecondVariable K u v) := by
    -- The slice subdifferential is exactly the textbook second partial subdifferential.
    simpa [hSecondEq] using hSliceClosed
  have hPartialBounded :
      Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v) := by
    -- Boundedness transports through the same slice identification.
    simpa [hSecondEq] using hSubNonemptyBounded.2
  have hPartialConvex :
      Convex ℝ (partialSubdifferentialInSecondVariable K u v) := by
    -- Convexity is likewise inherited from the slice subdifferential.
    simpa [hSecondEq] using hSliceConvex
  exact ⟨hPartialNonempty, hPartialClosed, hPartialBounded, hPartialConvex⟩

-- Proof sketch: apply Text 35.6.8 to obtain that `u` and `v` lie in the interiors of the
-- effective domains of the one-variable slices `u' ↦ K u' v` and `v' ↦ K u v'`. Then use the
-- one-variable interior-domain subdifferential theorem for the convex functions `u' ↦ -K u' v`
-- and `v' ↦ K u v` to conclude that the corresponding partial subdifferentials are nonempty,
-- closed, bounded, and convex.
/-- Text 35.6.9: let `K : ℝ^m × ℝ^n → \overline{ℝ}` be a proper saddle-function, and let
`(u, v) ∈ interior (dom K)`. Then the partial subdifferentials `∂₁ K(u, v) ⊆ ℝ^m` and
`∂₂ K(u, v) ⊆ ℝ^n` are nonempty, closed, bounded, convex sets. -/
theorem section35_text35_6_9
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    (hProper : ProperERealFunction (Function.uncurry K))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (erealDom (Function.uncurry K))) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
      IsClosed (partialSubdifferentialInFirstVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) ∧
      Convex ℝ (partialSubdifferentialInFirstVariable K u v) ∧
      Set.Nonempty (partialSubdifferentialInSecondVariable K u v) ∧
      IsClosed (partialSubdifferentialInSecondVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v) ∧
      Convex ℝ (partialSubdifferentialInSecondVariable K u v) := by
  rcases
      helperForText_35_6_9_firstPartial_nonempty_closed_bounded_convex
        (K := K) hSaddle hProper hInterior with
    ⟨hFirstNonempty, hFirstClosed, hFirstBounded, hFirstConvex⟩
  rcases
      helperForText_35_6_9_secondPartial_nonempty_closed_bounded_convex
        (K := K) hSaddle hProper hInterior with
    ⟨hSecondNonempty, hSecondClosed, hSecondBounded, hSecondConvex⟩
  -- Combine the two slice-wise Chapter 23 conclusions into the textbook product statement.
  exact
    ⟨hFirstNonempty, hFirstClosed, hFirstBounded, hFirstConvex,
      hSecondNonempty, hSecondClosed, hSecondBounded, hSecondConvex⟩


end Section35
end Chap07
