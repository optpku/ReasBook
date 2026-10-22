/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part18

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Theorem 35.8: the Chapter 34 coordinate effective-domain conditions are already
the separate `≠ ⊥` and `≠ ⊤` statements needed to conclude finiteness at a mixed point. -/
lemma helperForTheorem_35_8_finite_of_mem_effectiveDomains
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsGloballyConcaveConvexERealKernel K)
    {x : Fin m → ℝ} {y : Fin n → ℝ}
    (hxDom : x ∈ effectiveDomain₁ K)
    (hyDom : y ∈ effectiveDomain₂ K) :
    K x y ≠ (⊤ : EReal) ∧ K x y ≠ (⊥ : EReal) := by
  -- `dom₂ K` excludes `⊤` uniformly in the first coordinate, while `dom₁ K` excludes `⊥`
  -- uniformly in the second coordinate.
  exact ⟨lt_top_iff_ne_top.mp (hyDom x), bot_lt_iff_ne_bot.mp (hxDom y)⟩

/-- Helper for Theorem 35.8: singleton first/second partial data already shows that the base
point lies in `dom₁ K × dom₂ K`; what remains missing later is only a neighborhood upgrade of
these domain memberships. -/
lemma helperForTheorem_35_8_base_mem_effectiveDomains_of_singleton_partials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    u ∈ effectiveDomain₁ K ∧ v ∈ effectiveDomain₂ K := by
  let f : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  let g : (Fin n → ℝ) → EReal := K u
  have hf : ConvexFunction f := by
    -- The reflected first slice is convex because `K` is concave in the first variable.
    simpa [f] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v
  have hg : ConvexFunction g := by
    -- Fixing the first variable leaves a convex second slice.
    simpa [g] using hK.2 u
  rcases
      helperForTheorem_35_8_sliceDifferentiabilityWitnesses_of_singleton_partials
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFinite hFirstSingleton hSecondSingleton with
    ⟨hRefDiff, hSecondDiff⟩
  have hRefProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f :=
    (convexFunction_proper_and_mem_interior_of_differentiableAt f hf (-u) hRefDiff).1
  have hSecondProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    (convexFunction_proper_and_mem_interior_of_differentiableAt g hg v hSecondDiff).1
  constructor
  · intro y
    -- Properness of the honest second slice rules out `⊥` at every second coordinate.
    exact bot_lt_iff_ne_bot.mpr <| by
      simpa [g] using hSecondProper.2.2 y (by simp)
  · intro x
    -- Properness of the reflected first slice rules out `⊤` at every first coordinate.
    exact lt_top_iff_ne_top.mpr <| by
      have hRefNeBot : f (-x) ≠ (⊥ : EReal) := hRefProper.2.2 (-x) (by simp)
      simpa [f] using hRefNeBot

/-- Helper for Theorem 35.8: a pair of coordinate effective-domain memberships is exactly the
pair of universal no-`⊥` and no-`⊤` clauses needed later for the moved first and second slices. -/
lemma helperForTheorem_35_8_effectiveDomainPair_iff_universalMovedSliceClauses
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {x : Fin m → ℝ} {y : Fin n → ℝ} :
    (x ∈ effectiveDomain₁ K ∧ y ∈ effectiveDomain₂ K) ↔
      (∀ y' : Fin n → ℝ, K x y' ≠ (⊥ : EReal)) ∧
        ∀ x' : Fin m → ℝ, K x' y ≠ (⊤ : EReal) := by
  constructor
  · intro hDom
    constructor
    · intro y'
      -- Unpack `x ∈ dom₁ K` as the universal exclusion of `⊥` on the first moved slice.
      exact bot_lt_iff_ne_bot.mp (hDom.1 y')
    · intro x'
      -- Unpack `y ∈ dom₂ K` as the universal exclusion of `⊤` on the second moved slice.
      exact lt_top_iff_ne_top.mp (hDom.2 x')
  · intro hUniversal
    constructor
    · intro y'
      -- Repackage the universal no-`⊥` clause as membership in `effectiveDomain₁ K`.
      exact bot_lt_iff_ne_bot.mpr (hUniversal.1 y')
    · intro x'
      -- Repackage the universal no-`⊤` clause as membership in `effectiveDomain₂ K`.
      exact lt_top_iff_ne_top.mpr (hUniversal.2 x')

/-- Helper for Theorem 35.8: once `(u, v)` is already known to lie in `dom₁ K × dom₂ K`, every
translated second slice and every reflected translated first slice already satisfies the convexity
and nonempty-effective-domain half of the properness package. -/
lemma helperForTheorem_35_8_movedSlices_convex_and_nonemptyEffectiveDomains_of_baseEffectiveDomains
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (huDom : u ∈ effectiveDomain₁ K)
    (hvDom : v ∈ effectiveDomain₂ K) :
    ∀ t : ℝ,
      ConvexFunction (K (u + t • du)) ∧
        (convexFunctionEffectiveDomain (K (u + t • du))).Nonempty ∧
          ConvexFunction (K (u - t • du)) ∧
            (convexFunctionEffectiveDomain (K (u - t • du))).Nonempty ∧
              ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) ∧
                (convexFunctionEffectiveDomain
                  (fun x : Fin m → ℝ => -K (-x) (v + t • dv))).Nonempty ∧
                  ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v - t • dv)) ∧
                    (convexFunctionEffectiveDomain
                      (fun x : Fin m → ℝ => -K (-x) (v - t • dv))).Nonempty := by
  intro t
  have hPlusSecondConv : ConvexFunction (K (u + t • du)) := by
    -- Every second slice of a concave-convex kernel is convex.
    simpa using hK.2 (u + t • du)
  have hPlusSecondNonempty :
      (convexFunctionEffectiveDomain (K (u + t • du))).Nonempty := by
    -- The base second-coordinate point `v` stays in the effective domain of every moved second
    -- slice because `v ∈ dom₂ K`.
    exact ⟨v, hvDom (u + t • du)⟩
  have hMinusSecondConv : ConvexFunction (K (u - t • du)) := by
    -- The same convexity statement applies to the reflected translate in the first coordinate.
    simpa using hK.2 (u - t • du)
  have hMinusSecondNonempty :
      (convexFunctionEffectiveDomain (K (u - t • du))).Nonempty := by
    -- The witness `v` also works for the reflected moved second slice.
    exact ⟨v, hvDom (u - t • du)⟩
  have hPlusReflectedFirstConv :
      ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) := by
    -- Reflecting the first variable converts concavity into convexity for every moved
    -- second-coordinate slice.
    simpa using helperForText_35_6_6_reflectedFirstSlice_convex
      (K := K) hK (v + t • dv)
  have hPlusReflectedFirstNonempty :
      (convexFunctionEffectiveDomain
        (fun x : Fin m → ℝ => -K (-x) (v + t • dv))).Nonempty := by
    -- The reflected base point `-u` is an effective-domain witness because `u ∈ dom₁ K`.
    refine ⟨-u, ?_⟩
    -- Writing the witness point explicitly reduces the reflected effective-domain condition to the
    -- base-domain exclusion `K u (v + t • dv) ≠ ⊥`.
    change -K (-(-u)) (v + t • dv) < (⊤ : EReal)
    exact lt_top_iff_ne_top.mpr <| by
      simpa using (bot_lt_iff_ne_bot.mp (huDom (v + t • dv)))
  have hMinusReflectedFirstConv :
      ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v - t • dv)) := by
    -- The reflected convexity statement is symmetric under replacing `t` by `-t`.
    simpa using helperForText_35_6_6_reflectedFirstSlice_convex
      (K := K) hK (v - t • dv)
  have hMinusReflectedFirstNonempty :
      (convexFunctionEffectiveDomain
        (fun x : Fin m → ℝ => -K (-x) (v - t • dv))).Nonempty := by
    -- The same witness `-u` lies in the effective domain of the reflected moved first slice.
    refine ⟨-u, ?_⟩
    -- The reflected minus-slice case is identical after expanding the witness point.
    change -K (-(-u)) (v - t • dv) < (⊤ : EReal)
    exact lt_top_iff_ne_top.mpr <| by
      simpa using (bot_lt_iff_ne_bot.mp (huDom (v - t • dv)))
  exact ⟨hPlusSecondConv, hPlusSecondNonempty, hMinusSecondConv, hMinusSecondNonempty,
    hPlusReflectedFirstConv, hPlusReflectedFirstNonempty, hMinusReflectedFirstConv,
    hMinusReflectedFirstNonempty⟩

/-- Helper for Theorem 35.8: once a short ray from `(u, v)` is known to stay inside
`dom₁ K × dom₂ K`, Chapter 34 already turns that domain information into finiteness of the mixed
points on the same ray. -/
lemma helperForTheorem_35_8_small_mixed_finiteness_of_shortRay_mem_effectiveDomains
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hShortRayDomains :
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ t : ℝ, 0 < t → t < ρ →
          (u + t • du) ∈ effectiveDomain₁ K ∧
            (v + t • dv) ∈ effectiveDomain₂ K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t : ℝ, 0 < t → t < ρ →
        K (u + t • du) (v + t • dv) ≠ (⊤ : EReal) ∧
          K (u + t • du) (v + t • dv) ≠ (⊥ : EReal) := by
  rcases hShortRayDomains with ⟨ρ, hρpos, hShortRayDomains⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro t ht htrho
  rcases hShortRayDomains t ht htrho with ⟨huDom, hvDom⟩
  -- The general Chapter 34 domain-to-finiteness bridge applies as soon as the moved point lies in
  -- `dom₁ K × dom₂ K`.
  exact
    helperForTheorem_35_8_finite_of_mem_effectiveDomains
      (K := K) hK huDom hvDom

/-- Helper for Theorem 35.8: the already-proved reflected axis finiteness radius can be
repackaged as short-ray membership in the one-variable slice effective domains through `v` and
`u`. -/
lemma helperForTheorem_35_8_small_reflected_points_mem_sliceEffectiveDomains_of_singletonSliceData
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t : ℝ, 0 < t → t < ρ →
        (u + t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) ∧
          (u - t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) ∧
            (v + t • dv) ∈ convexFunctionEffectiveDomain (K u) ∧
              (v - t • dv) ∈ convexFunctionEffectiveDomain (K u) := by
  rcases
      helperForTheorem_35_8_small_reflected_axis_finiteness_of_singletonSliceData
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        (du := du) (dv := dv) hK hFinite hFirstSingleton hSecondSingleton with
    ⟨ρ, hρpos, hAxisFinite⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro t ht htrho
  rcases hAxisFinite t ht htrho with ⟨hxFinite, hxRefFinite, hyFinite, hyRefFinite⟩
  have hxSliceDom :
      (u + t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) := by
    -- The positive first-coordinate point already avoids `⊥` in the fixed second slice.
    exact bot_lt_iff_ne_bot.mpr hxFinite.2
  have hxRefSliceDom :
      (u - t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) := by
    -- The reflected first-coordinate point has the same slice finiteness property.
    exact bot_lt_iff_ne_bot.mpr hxRefFinite.2
  have hySliceDom :
      (v + t • dv) ∈ convexFunctionEffectiveDomain (K u) := by
    -- The positive second-coordinate point already avoids `⊤` in the fixed first slice.
    exact lt_top_iff_ne_top.mpr hyFinite.1
  have hyRefSliceDom :
      (v - t • dv) ∈ convexFunctionEffectiveDomain (K u) := by
    -- The reflected second-coordinate point has the same slice finiteness property.
    exact lt_top_iff_ne_top.mpr hyRefFinite.1
  exact ⟨hxSliceDom, hxRefSliceDom, hySliceDom, hyRefSliceDom⟩

/-- Helper for Theorem 35.8: once the base point already lies in `dom₁ K × dom₂ K`, the
short-ray fixed-slice data supplies concrete finite reference points on each moved slice. What
still remains later is only the universal `≠ ⊥` / `≠ ⊤` upgrade required by `effectiveDomain₁`
and `effectiveDomain₂`. -/
lemma helperForTheorem_35_8_movedSlices_finite_referencePoints_of_baseDomains_and_sliceRayDomains
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (huBaseDom : u ∈ effectiveDomain₁ K)
    (hvBaseDom : v ∈ effectiveDomain₂ K)
    (hSliceRayDomains :
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ t : ℝ, 0 < t → t < ρ →
          (u + t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) ∧
            (u - t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) ∧
              (v + t • dv) ∈ convexFunctionEffectiveDomain (K u) ∧
                (v - t • dv) ∈ convexFunctionEffectiveDomain (K u)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t : ℝ, 0 < t → t < ρ →
        (K (u + t • du) v ≠ (⊤ : EReal) ∧ K (u + t • du) v ≠ (⊥ : EReal)) ∧
          (K (u - t • du) v ≠ (⊤ : EReal) ∧ K (u - t • du) v ≠ (⊥ : EReal)) ∧
            (K u (v + t • dv) ≠ (⊤ : EReal) ∧ K u (v + t • dv) ≠ (⊥ : EReal)) ∧
              (K u (v - t • dv) ≠ (⊤ : EReal) ∧ K u (v - t • dv) ≠ (⊥ : EReal)) ∧
                v ∈ convexFunctionEffectiveDomain (K (u + t • du)) ∧
                  v ∈ convexFunctionEffectiveDomain (K (u - t • du)) ∧
                    (-u) ∈ convexFunctionEffectiveDomain
                      (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) ∧
                      (-u) ∈ convexFunctionEffectiveDomain
                        (fun x : Fin m → ℝ => -K (-x) (v - t • dv)) := by
  rcases hSliceRayDomains with ⟨ρ, hρpos, hSliceRayDomains⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro t ht htrho
  rcases hSliceRayDomains t ht htrho with ⟨hxPlusSliceDom, hxMinusSliceDom, hyPlusSliceDom,
    hyMinusSliceDom⟩
  have hxPlusTop : K (u + t • du) v ≠ (⊤ : EReal) := by
    -- The base second-coordinate witness `v ∈ dom₂ K` already keeps the moved first slice away
    -- from `⊤` at the reference point `v`.
    exact lt_top_iff_ne_top.mp (hvBaseDom (u + t • du))
  have hxPlusBot : K (u + t • du) v ≠ (⊥ : EReal) := by
    -- The short-ray slice-domain data supplies the complementary `≠ ⊥` half at the same point.
    exact bot_lt_iff_ne_bot.mp hxPlusSliceDom
  have hxMinusTop : K (u - t • du) v ≠ (⊤ : EReal) := by
    -- The reflected moved first slice uses the same base second-coordinate witness.
    exact lt_top_iff_ne_top.mp (hvBaseDom (u - t • du))
  have hxMinusBot : K (u - t • du) v ≠ (⊥ : EReal) := by
    -- The reflected short-ray slice-domain point is finite in the fixed second slice as well.
    exact bot_lt_iff_ne_bot.mp hxMinusSliceDom
  have hyPlusTop : K u (v + t • dv) ≠ (⊤ : EReal) := by
    -- The short-ray second-slice effective-domain datum already excludes `⊤`.
    exact lt_top_iff_ne_top.mp hyPlusSliceDom
  have hyPlusBot : K u (v + t • dv) ≠ (⊥ : EReal) := by
    -- The base first-coordinate witness `u ∈ dom₁ K` excludes `⊥` at every second coordinate.
    exact bot_lt_iff_ne_bot.mp (huBaseDom (v + t • dv))
  have hyMinusTop : K u (v - t • dv) ≠ (⊤ : EReal) := by
    -- The reflected short-ray second-slice point also avoids `⊤`.
    exact lt_top_iff_ne_top.mp hyMinusSliceDom
  have hyMinusBot : K u (v - t • dv) ≠ (⊥ : EReal) := by
    -- The same base first-coordinate witness excludes `⊥` on the reflected ray.
    exact bot_lt_iff_ne_bot.mp (huBaseDom (v - t • dv))
  have hvPlusMoved : v ∈ convexFunctionEffectiveDomain (K (u + t • du)) := by
    -- Repackage the already-known `≠ ⊤` statement as a concrete effective-domain witness for the
    -- moved second slice.
    exact lt_top_iff_ne_top.mpr hxPlusTop
  have hvMinusMoved : v ∈ convexFunctionEffectiveDomain (K (u - t • du)) := by
    -- The reflected moved second slice has the same concrete witness point `v`.
    exact lt_top_iff_ne_top.mpr hxMinusTop
  have huPlusMoved : (-u) ∈ convexFunctionEffectiveDomain
      (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) := by
    -- For the reflected moved first slice, the fixed witness point is `-u`, and base membership
    -- in `dom₁ K` supplies exactly the `≠ ⊥` clause needed after reflection.
    change -K (-(-u)) (v + t • dv) < (⊤ : EReal)
    exact lt_top_iff_ne_top.mpr <| by
      simpa using hyPlusBot
  have huMinusMoved : (-u) ∈ convexFunctionEffectiveDomain
      (fun x : Fin m → ℝ => -K (-x) (v - t • dv)) := by
    -- The reflected minus-slice case is identical with `v - t • dv`.
    change -K (-(-u)) (v - t • dv) < (⊤ : EReal)
    exact lt_top_iff_ne_top.mpr <| by
      simpa using hyMinusBot
  -- At the common short-ray radius, every moved slice now has a concrete finite reference point;
  -- later only the universal coordinate-domain upgrade remains.
  repeat' constructor
  · exact hxPlusTop
  · exact hxPlusBot
  · exact hxMinusTop
  · exact hxMinusBot
  · exact hyPlusTop
  · exact hyPlusBot
  · exact hyMinusTop
  · exact hyMinusBot
  · exact hvPlusMoved
  · exact hvMinusMoved
  · exact huPlusMoved
  · exact huMinusMoved

/-- Helper for Theorem 35.8: singleton partial data already packages the positive-ray moved-slice
convexity, nonempty effective domains, and concrete finite reference points that are available
before the missing properness upgrade. -/
lemma helperForTheorem_35_8_positiveRayMovedSliceWitnesses_of_singleton_partials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t : ℝ, 0 < t → t < ρ →
        ConvexFunction (K (u + t • du)) ∧
          (convexFunctionEffectiveDomain (K (u + t • du))).Nonempty ∧
            ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) ∧
              (convexFunctionEffectiveDomain
                (fun x : Fin m → ℝ => -K (-x) (v + t • dv))).Nonempty ∧
                (K (u + t • du) v ≠ (⊤ : EReal) ∧
                  K (u + t • du) v ≠ (⊥ : EReal)) ∧
                  (K u (v + t • dv) ≠ (⊤ : EReal) ∧
                    K u (v + t • dv) ≠ (⊥ : EReal)) ∧
                    v ∈ convexFunctionEffectiveDomain (K (u + t • du)) ∧
                      (-u) ∈ convexFunctionEffectiveDomain
                        (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) := by
  rcases
      helperForTheorem_35_8_base_mem_effectiveDomains_of_singleton_partials
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFinite hFirstSingleton hSecondSingleton with
    ⟨huBaseDom, hvBaseDom⟩
  have hMovedSlicesConvex :
      ∀ t : ℝ,
        ConvexFunction (K (u + t • du)) ∧
          (convexFunctionEffectiveDomain (K (u + t • du))).Nonempty ∧
            ConvexFunction (K (u - t • du)) ∧
              (convexFunctionEffectiveDomain (K (u - t • du))).Nonempty ∧
                ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) ∧
                  (convexFunctionEffectiveDomain
                    (fun x : Fin m → ℝ => -K (-x) (v + t • dv))).Nonempty ∧
                    ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v - t • dv)) ∧
                      (convexFunctionEffectiveDomain
                        (fun x : Fin m → ℝ => -K (-x) (v - t • dv))).Nonempty :=
    helperForTheorem_35_8_movedSlices_convex_and_nonemptyEffectiveDomains_of_baseEffectiveDomains
      (K := K) (u := u) (v := v) (du := du) (dv := dv) hK huBaseDom hvBaseDom
  have hSliceRayDomains :
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ t : ℝ, 0 < t → t < ρ →
          (u + t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) ∧
            (u - t • du) ∈ concaveFunctionEffectiveDomain (fun x => K x v) ∧
              (v + t • dv) ∈ convexFunctionEffectiveDomain (K u) ∧
                (v - t • dv) ∈ convexFunctionEffectiveDomain (K u) :=
    helperForTheorem_35_8_small_reflected_points_mem_sliceEffectiveDomains_of_singletonSliceData
      (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
      (du := du) (dv := dv) hK hFinite hFirstSingleton hSecondSingleton
  rcases
      helperForTheorem_35_8_movedSlices_finite_referencePoints_of_baseDomains_and_sliceRayDomains
        (K := K) (u := u) (v := v) (du := du) (dv := dv)
        huBaseDom hvBaseDom hSliceRayDomains with
    ⟨ρ, hρpos, hMovedReferencePoints⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro t ht htrho
  rcases hMovedSlicesConvex t with
    ⟨hPlusSecondConv, hPlusSecondNonempty, _hMinusSecondConv, _hMinusSecondNonempty,
      hPlusReflectedFirstConv, hPlusReflectedFirstNonempty, _hMinusReflectedFirstConv,
      _hMinusReflectedFirstNonempty⟩
  have hMovedReferencePoints_t := hMovedReferencePoints t ht htrho
  have hxPlusTop : K (u + t • du) v ≠ (⊤ : EReal) := hMovedReferencePoints_t.1.1
  have hxPlusBot : K (u + t • du) v ≠ (⊥ : EReal) := hMovedReferencePoints_t.1.2
  have hyPlusTop : K u (v + t • dv) ≠ (⊤ : EReal) :=
    hMovedReferencePoints_t.2.2.1.1
  have hyPlusBot : K u (v + t • dv) ≠ (⊥ : EReal) :=
    hMovedReferencePoints_t.2.2.1.2
  have hvPlusMoved : v ∈ convexFunctionEffectiveDomain (K (u + t • du)) :=
    hMovedReferencePoints_t.2.2.2.2.1
  have huPlusMoved :
      (-u) ∈ convexFunctionEffectiveDomain
        (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) :=
    hMovedReferencePoints_t.2.2.2.2.2.2.1
  -- This isolates exactly the positive-ray data already available locally: each moved slice is
  -- convex, has a nonempty effective domain, and comes with an explicit finite reference point.
  exact ⟨hPlusSecondConv, hPlusSecondNonempty, hPlusReflectedFirstConv,
    hPlusReflectedFirstNonempty, ⟨hxPlusTop, hxPlusBot⟩, ⟨hyPlusTop, hyPlusBot⟩, hvPlusMoved,
    huPlusMoved⟩

/-- Helper for Theorem 35.8: singleton first/second partial data should keep sufficiently small
mixed secants on any fixed ray from `(u, v)` inside the finite part of `EReal`. -/
lemma helperForTheorem_35_8_small_mixed_secants_finite_of_universalMovedSliceClauses
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hUniversalMovedSlices :
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ t : ℝ, 0 < t → t < ρ →
          (∀ y : Fin n → ℝ, K (u + t • du) y ≠ (⊥ : EReal)) ∧
            ∀ x : Fin m → ℝ, K x (v + t • dv) ≠ (⊤ : EReal)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t : ℝ, 0 < t → t < ρ →
        K (u + t • du) (v + t • dv) ≠ (⊤ : EReal) ∧
          K (u + t • du) (v + t • dv) ≠ (⊥ : EReal) := by
  rcases hUniversalMovedSlices with ⟨ρ, hρpos, hUniversalMovedSlices⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro t ht htrho
  have hMovedDomains :
      (u + t • du) ∈ effectiveDomain₁ K ∧
        (v + t • dv) ∈ effectiveDomain₂ K :=
    (helperForTheorem_35_8_effectiveDomainPair_iff_universalMovedSliceClauses
      (K := K) (x := u + t • du) (y := v + t • dv)).2 <|
      hUniversalMovedSlices t ht htrho
  -- The universal moved-slice clauses are exactly the coordinate effective-domain hypotheses
  -- required by the generic Chapter 34 finiteness bridge.
  exact
    helperForTheorem_35_8_finite_of_mem_effectiveDomains
      (K := K) hK hMovedDomains.1 hMovedDomains.2

/-- Helper for Theorem 35.8: singleton first/second partial data should force a uniform short-ray
universal no-`⊥` / no-`⊤` statement for the moved slices through `(u, v)`. -/
lemma helperForTheorem_35_8_uniformMovedSlices_noBot_noTop_of_preparedMovedSliceInterior
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hPreparedMovedSlices :
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ t : ℝ, 0 < t → t < ρ →
          ConvexFunction (K (u + t • du)) ∧
            (convexFunctionEffectiveDomain (K (u + t • du))).Nonempty ∧
              ConvexFunction (fun x : Fin m → ℝ => -K (-x) (v + t • dv)) ∧
                (convexFunctionEffectiveDomain
                  (fun x : Fin m → ℝ => -K (-x) (v + t • dv))).Nonempty ∧
                  (K (u + t • du) v ≠ (⊤ : EReal) ∧
                    K (u + t • du) v ≠ (⊥ : EReal)) ∧
                    (K u (v + t • dv) ≠ (⊤ : EReal) ∧
                      K u (v + t • dv) ≠ (⊥ : EReal)) ∧
                      v ∈ convexFunctionEffectiveDomain (K (u + t • du)) ∧
                        (-u) ∈ convexFunctionEffectiveDomain
                          (fun x : Fin m → ℝ => -K (-x) (v + t • dv)))
    (hMovedInterior :
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ t : ℝ, 0 < t → t < ρ →
          v ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K (u + t • du))) ∧
            (-u) ∈ interior
              (effectiveDomain (Set.univ : Set (Fin m → ℝ))
                (fun x : Fin m → ℝ => -K (-x) (v + t • dv)))) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t : ℝ, 0 < t → t < ρ →
        (∀ y : Fin n → ℝ, K (u + t • du) y ≠ (⊥ : EReal)) ∧
          ∀ x : Fin m → ℝ, K x (v + t • dv) ≠ (⊤ : EReal) := by
  rcases hPreparedMovedSlices with ⟨ρPrepared, hρPreparedPos, hPreparedMovedSlices⟩
  rcases hMovedInterior with ⟨ρInterior, hρInteriorPos, hMovedInterior⟩
  refine ⟨min ρPrepared ρInterior, lt_min hρPreparedPos hρInteriorPos, ?_⟩
  intro t ht htrho
  have htrhoPrepared : t < ρPrepared := lt_of_lt_of_le htrho (min_le_left _ _)
  have htrhoInterior : t < ρInterior := lt_of_lt_of_le htrho (min_le_right _ _)
  rcases hPreparedMovedSlices t ht htrhoPrepared with
    ⟨hSecondConv, _hSecondNonempty, hReflectedFirstConv, _hReflectedFirstNonempty,
      hMovedSecondBaseFinite, hMovedFirstBaseFinite, _hvMovedDom, _huMovedDom⟩
  rcases hMovedInterior t ht htrhoInterior with ⟨hvInterior, huInterior⟩
  let g : (Fin n → ℝ) → EReal := K (u + t • du)
  let f : (Fin m → ℝ) → EReal := fun x : Fin m → ℝ => -K (-x) (v + t • dv)
  have hSecondProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    -- Interior membership plus the already-prepared finite base value upgrades the moved second
    -- slice to a proper convex function on all of `ℝ^n`.
    refine
      helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
        (x := v) hSecondConv ?_ ?_
    · simpa [g] using hvInterior
    · simpa [g] using hMovedSecondBaseFinite.2
  have hReflectedFirstProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
    -- The same Chapter 25 properness bridge applies to the reflected first slice.
    refine
      helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
        (x := -u) hReflectedFirstConv ?_ ?_
    · simpa [f] using huInterior
    · simpa [f] using hMovedFirstBaseFinite.1
  constructor
  · intro y
    -- Properness of the moved second slice excludes `⊥` at every second-coordinate point.
    simpa [g] using hSecondProper.2.2 y (by simp)
  · intro x
    -- Properness of the reflected first slice excludes `⊥`, which is exactly `K x (v+t•dv) ≠ ⊤`.
    have hRefNeBot : f (-x) ≠ (⊥ : EReal) := hReflectedFirstProper.2.2 (-x) (by simp)
    simpa [f] using hRefNeBot

/-- Helper for Theorem 35.8: every open neighborhood of a point contains a smaller ball that is
stable under reflection through that point. -/
lemma helperForTheorem_35_8_reflectionStableBall_subset_of_open
    {k : ℕ} {c : Fin k → ℝ} {S : Set (Fin k → ℝ)}
    (hSopen : IsOpen S) (hcS : c ∈ S) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball c ε ⊆ S ∧
      ∀ z : Fin k → ℝ, z ∈ Metric.ball c ε → 2 • c - z ∈ S := by
  rcases Metric.mem_nhds_iff.mp (hSopen.mem_nhds hcS) with ⟨ε, hε, hBall⟩
  refine ⟨ε, hε, hBall, ?_⟩
  intro z hz
  -- Reflection preserves the ball centered at `c`, so the smaller ball stays inside `S`.
  exact hBall <|
    helperForTheorem_35_8_reflection_mem_ball (c := c) (x := z) (ε := ε) hz

/-- Helper for Theorem 35.8: once a positive-radius ball lies in the effective domain, its center
is an interior point of that effective domain. -/
lemma helperForTheorem_35_8_memInterior_effectiveDomain_of_ball_subset
    {k : ℕ} {f : (Fin k → ℝ) → EReal} {c : Fin k → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (hBall :
      Metric.ball c ε ⊆ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f) :
    c ∈ interior (effectiveDomain (Set.univ : Set (Fin k → ℝ)) f) := by
  -- The given ball is an open neighborhood of `c` already contained in the effective domain.
  exact mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (Metric.ball_mem_nhds c hε) hBall

/-- Helper for Theorem 35.8: pointwise exclusion of `⊤` on a ball is exactly the ballwise
effective-domain inclusion needed for a moved second slice. -/
lemma helperForTheorem_35_8_ball_subset_effectiveDomain_of_pointwise_neTop
    {k : ℕ} {f : (Fin k → ℝ) → EReal} {c : Fin k → ℝ} {ε : ℝ}
    (hNoTop : ∀ y : Fin k → ℝ, y ∈ Metric.ball c ε → f y ≠ (⊤ : EReal)) :
    Metric.ball c ε ⊆ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f := by
  intro y hy
  -- On `Set.univ`, effective-domain membership is just the exclusion of `⊤`.
  simpa [effectiveDomain_eq, lt_top_iff_ne_top] using hNoTop y hy

/-- Helper for Theorem 35.8: pointwise exclusion of `⊥` on a ball around `u` is exactly the
ballwise effective-domain inclusion for the reflected moved first slice around `-u`. -/
lemma helperForTheorem_35_8_reflectedBall_subset_effectiveDomain_of_pointwise_neBot
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {y : Fin n → ℝ} {ε : ℝ}
    (hNoBot : ∀ x : Fin m → ℝ, x ∈ Metric.ball u ε → K x y ≠ (⊥ : EReal)) :
    Metric.ball (-u) ε ⊆
      effectiveDomain (Set.univ : Set (Fin m → ℝ))
        (fun x : Fin m → ℝ => -K (-x) y) := by
  intro z hz
  have hzDist : dist z (-u) < ε := by
    simpa [Metric.mem_ball] using hz
  have hDistEq : dist (-z) u = dist z (-u) := by
    simpa using dist_neg_neg z (-u)
  have hNegDist : dist (-z) u < ε := by
    -- Negation identifies the ball around `-u` with the ball around `u`.
    rwa [hDistEq]
  have hNegMem : -z ∈ Metric.ball u ε := by
    simpa [Metric.mem_ball] using hNegDist
  -- After reflection, effective-domain membership is exactly the exclusion of `⊥`.
  simpa [effectiveDomain_eq, lt_top_iff_ne_top] using hNoBot (-z) hNegMem

/-- Helper for Theorem 35.8: an alternating reflected checkerboard already makes the mixed saddle
quotient at unit step equal to `⊤` or `⊥`. -/
lemma helperForTheorem_35_8_checkerboardForcesInfiniteMixedQuotient_atUnitStep
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {x : Fin m → ℝ} {y : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hChecker :
      (K x y = (⊤ : EReal) ∧
          K (2 • u - x) y = (⊥ : EReal) ∧
          K (2 • u - x) (2 • v - y) = (⊤ : EReal) ∧
          K x (2 • v - y) = (⊥ : EReal)) ∨
        (K x y = (⊥ : EReal) ∧
          K (2 • u - x) y = (⊤ : EReal) ∧
          K (2 • u - x) (2 • v - y) = (⊥ : EReal) ∧
          K x (2 • v - y) = (⊤ : EReal))) :
    saddleDirectionalDifferenceQuotientAt K u v (x - u) (y - v) 1 = (⊤ : EReal) ∨
      saddleDirectionalDifferenceQuotientAt K u v (x - u) (y - v) 1 = (⊥ : EReal) := by
  have hxPlus : u + (1 : ℝ) • (x - u) = x := by
    -- At unit step, the positive first ray lands exactly at the chosen corner `x`.
    ext i
    simp [sub_eq_add_neg]
  have hxMinus : u - (1 : ℝ) • (x - u) = 2 • u - x := by
    -- The reflected first ray lands at the symmetric corner across `u`.
    ext i
    simp [two_smul, sub_eq_add_neg]
    ring
  have hyPlus : v + (1 : ℝ) • (y - v) = y := by
    -- The positive second ray lands exactly at the chosen corner `y`.
    ext j
    simp [sub_eq_add_neg]
  have hyMinus : v - (1 : ℝ) • (y - v) = 2 • v - y := by
    -- The reflected second ray lands at the symmetric corner across `v`.
    ext j
    simp [two_smul, sub_eq_add_neg]
    ring
  have hChecker' :
      let xPlus : Fin m → ℝ := u + (1 : ℝ) • (x - u)
      let xMinus : Fin m → ℝ := u - (1 : ℝ) • (x - u)
      let yPlus : Fin n → ℝ := v + (1 : ℝ) • (y - v)
      let yMinus : Fin n → ℝ := v - (1 : ℝ) • (y - v)
      (K xPlus yPlus = (⊤ : EReal) ∧
            K xMinus yPlus = (⊥ : EReal) ∧
            K xMinus yMinus = (⊤ : EReal) ∧
            K xPlus yMinus = (⊥ : EReal)) ∨
          (K xPlus yPlus = (⊥ : EReal) ∧
            K xMinus yPlus = (⊤ : EReal) ∧
            K xMinus yMinus = (⊥ : EReal) ∧
            K xPlus yMinus = (⊤ : EReal)) := by
    rcases hChecker with hTop | hBot
    · rcases hTop with ⟨hxy, hxyRef, hRefRef, hyRef⟩
      left
      -- Rewrite the unit-step corners back to the original checkerboard points.
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hxPlus, hyPlus]
        exact hxy
      · rw [hxMinus, hyPlus]
        exact hxyRef
      · rw [hxMinus, hyMinus]
        exact hRefRef
      · rw [hxPlus, hyMinus]
        exact hyRef
    · rcases hBot with ⟨hxy, hxyRef, hRefRef, hyRef⟩
      right
      -- The bottom-corner branch rewrites in the same way.
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hxPlus, hyPlus]
        exact hxy
      · rw [hxMinus, hyPlus]
        exact hxyRef
      · rw [hxMinus, hyMinus]
        exact hRefRef
      · rw [hxPlus, hyMinus]
        exact hyRef
  -- The common-shrink lemma at `r = 1` turns the reflected checkerboard directly into an
  -- infinite mixed quotient.
  exact
    helperForTheorem_35_8_checkerboardForcesInfiniteMixedQuotient_afterCommonShrink
      (K := K) (u := u) (v := v) (x := x) (y := y) (r := 1) hFinite zero_lt_one hChecker'

/-- Helper for Theorem 35.8: a bad fixed-time checkerboard on the second-coordinate reflection
pair already forces the mixed quotient along `(t • du, y - v)` to be infinite at unit step. -/
lemma helperForTheorem_35_8_fixedTimeSecondBall_checkerboardForcesInfiniteMixedQuotient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (du : Fin m → ℝ)
    {t : ℝ} {y : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hChecker :
      (K (u + t • du) y = (⊤ : EReal) ∧
          K (u - t • du) y = (⊥ : EReal) ∧
          K (u - t • du) (2 • v - y) = (⊤ : EReal) ∧
          K (u + t • du) (2 • v - y) = (⊥ : EReal)) ∨
        (K (u + t • du) y = (⊥ : EReal) ∧
          K (u - t • du) y = (⊤ : EReal) ∧
          K (u - t • du) (2 • v - y) = (⊥ : EReal) ∧
          K (u + t • du) (2 • v - y) = (⊤ : EReal))) :
    saddleDirectionalDifferenceQuotientAt K u v (t • du) (y - v) 1 = (⊤ : EReal) ∨
      saddleDirectionalDifferenceQuotientAt K u v (t • du) (y - v) 1 = (⊥ : EReal) := by
  have hReflectedFirstPoint : 2 • u - (u + t • du) = u - t • du := by
    -- Reflecting `u + t • du` across `u` lands at `u - t • du`.
    ext i
    simp [two_smul, sub_eq_add_neg]
    ring
  have hChecker' :
      (K (u + t • du) y = (⊤ : EReal) ∧
          K (2 • u - (u + t • du)) y = (⊥ : EReal) ∧
          K (2 • u - (u + t • du)) (2 • v - y) = (⊤ : EReal) ∧
          K (u + t • du) (2 • v - y) = (⊥ : EReal)) ∨
        (K (u + t • du) y = (⊥ : EReal) ∧
          K (2 • u - (u + t • du)) y = (⊤ : EReal) ∧
          K (2 • u - (u + t • du)) (2 • v - y) = (⊥ : EReal) ∧
          K (u + t • du) (2 • v - y) = (⊤ : EReal)) := by
    rcases hChecker with hTop | hBot
    · rcases hTop with ⟨h1, h2, h3, h4⟩
      left
      -- Rewrite only the reflected first-coordinate point.
      refine ⟨h1, ?_, ?_, h4⟩
      · rw [hReflectedFirstPoint]
        exact h2
      · rw [hReflectedFirstPoint]
        exact h3
    · rcases hBot with ⟨h1, h2, h3, h4⟩
      right
      -- The reflected first-coordinate rewrite is identical in the opposite branch.
      refine ⟨h1, ?_, ?_, h4⟩
      · rw [hReflectedFirstPoint]
        exact h2
      · rw [hReflectedFirstPoint]
        exact h3
  -- This is exactly the unit-step checkerboard lemma with `x = u + t • du`.
  simpa [hReflectedFirstPoint, sub_eq_add_neg] using
    helperForTheorem_35_8_checkerboardForcesInfiniteMixedQuotient_atUnitStep
      (K := K) (u := u) (v := v) (x := u + t • du) (y := y) hFinite hChecker'

/-- Helper for Theorem 35.8: a bad fixed-time checkerboard on the first-coordinate reflection pair
already forces the mixed quotient along `(x - u, t • dv)` to be infinite at unit step. -/
lemma helperForTheorem_35_8_fixedTimeFirstBall_checkerboardForcesInfiniteMixedQuotient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (dv : Fin n → ℝ)
    {t : ℝ} {x : Fin m → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hChecker :
      (K x (v + t • dv) = (⊤ : EReal) ∧
          K (2 • u - x) (v + t • dv) = (⊥ : EReal) ∧
          K (2 • u - x) (v - t • dv) = (⊤ : EReal) ∧
          K x (v - t • dv) = (⊥ : EReal)) ∨
        (K x (v + t • dv) = (⊥ : EReal) ∧
          K (2 • u - x) (v + t • dv) = (⊤ : EReal) ∧
          K (2 • u - x) (v - t • dv) = (⊥ : EReal) ∧
          K x (v - t • dv) = (⊤ : EReal))) :
    saddleDirectionalDifferenceQuotientAt K u v (x - u) (t • dv) 1 = (⊤ : EReal) ∨
      saddleDirectionalDifferenceQuotientAt K u v (x - u) (t • dv) 1 = (⊥ : EReal) := by
  have hReflectedSecondPoint : 2 • v - (v + t • dv) = v - t • dv := by
    -- Reflecting `v + t • dv` across `v` lands at `v - t • dv`.
    ext j
    simp [two_smul, sub_eq_add_neg]
    ring
  have hChecker' :
      (K x (v + t • dv) = (⊤ : EReal) ∧
          K (2 • u - x) (v + t • dv) = (⊥ : EReal) ∧
          K (2 • u - x) (2 • v - (v + t • dv)) = (⊤ : EReal) ∧
          K x (2 • v - (v + t • dv)) = (⊥ : EReal)) ∨
        (K x (v + t • dv) = (⊥ : EReal) ∧
          K (2 • u - x) (v + t • dv) = (⊤ : EReal) ∧
          K (2 • u - x) (2 • v - (v + t • dv)) = (⊥ : EReal) ∧
          K x (2 • v - (v + t • dv)) = (⊤ : EReal)) := by
    rcases hChecker with hTop | hBot
    · rcases hTop with ⟨h1, h2, h3, h4⟩
      left
      -- Rewrite only the reflected second-coordinate point.
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [hReflectedSecondPoint]
        exact h3
      · rw [hReflectedSecondPoint]
        exact h4
    · rcases hBot with ⟨h1, h2, h3, h4⟩
      right
      -- The reflected second-coordinate rewrite is identical in the opposite branch.
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [hReflectedSecondPoint]
        exact h3
      · rw [hReflectedSecondPoint]
        exact h4
  -- This is the same unit-step reduction with `y = v + t • dv`.
  simpa [hReflectedSecondPoint, sub_eq_add_neg] using
    helperForTheorem_35_8_checkerboardForcesInfiniteMixedQuotient_atUnitStep
      (K := K) (u := u) (v := v) (x := x) (y := v + t • dv) hFinite hChecker'

/-- Helper for Theorem 35.8: once the four reflected axis values are finite, any extreme value at
the mixed corner `K x y` already normalizes to one of the two reflected checkerboard branches. -/
lemma helperForTheorem_35_8_extremeMixedCorner_forces_reflectedCheckerboard
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {x : Fin m → ℝ} {y : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hxFinite : K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal))
    (hxRefFinite :
      K (2 • u - x) v ≠ (⊤ : EReal) ∧ K (2 • u - x) v ≠ (⊥ : EReal))
    (hyFinite : K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal))
    (hyRefFinite :
      K u (2 • v - y) ≠ (⊤ : EReal) ∧ K u (2 • v - y) ≠ (⊥ : EReal))
    (hxyExtreme : K x y = (⊤ : EReal) ∨ K x y = (⊥ : EReal)) :
    (K x y = (⊤ : EReal) ∧
        K (2 • u - x) y = (⊥ : EReal) ∧
        K (2 • u - x) (2 • v - y) = (⊤ : EReal) ∧
        K x (2 • v - y) = (⊥ : EReal)) ∨
      (K x y = (⊥ : EReal) ∧
        K (2 • u - x) y = (⊤ : EReal) ∧
        K (2 • u - x) (2 • v - y) = (⊥ : EReal) ∧
        K x (2 • v - y) = (⊤ : EReal)) := by
  rcases hxyExtreme with hxyTop | hxyBot
  · -- A top mixed corner propagates immediately to the first reflected checkerboard branch.
    rcases
        helperForTheorem_35_8_topCorner_forces_checkerboard
          (K := K) (u := u) (v := v) (x := x) (y := y) hK
          hxFinite hxRefFinite hyFinite hyRefFinite hxyTop with
      ⟨hxRefyBot, hxRefyRefTop, hxyRefBot⟩
    exact Or.inl ⟨hxyTop, hxRefyBot, hxRefyRefTop, hxyRefBot⟩
  · -- A bottom mixed corner gives the opposite reflected checkerboard branch.
    rcases
        helperForTheorem_35_8_botCorner_forces_checkerboard
          (K := K) (u := u) (v := v) (x := x) (y := y) hK
          hxFinite hxRefFinite hyFinite hyRefFinite hxyBot with
      ⟨hxRefyTop, hxRefyRefBot, hxyRefTop⟩
    exact Or.inr ⟨hxyBot, hxRefyTop, hxRefyRefBot, hxyRefTop⟩


end Section35
end Chap07
