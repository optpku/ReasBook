/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part20

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Theorem 35.8: a finite open rectangle immediately gives interior membership in the
saddle effective domain. -/
lemma helperForTheorem_35_8_memInterior_saddleFunctionEffectiveDomain_of_finiteRectangle
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCopen : IsOpen C) (huC : u ∈ C)
    (hDopen : IsOpen D) (hvD : v ∈ D)
    (hFinite :
      ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal)) :
    (u, v) ∈ interior (saddleFunctionEffectiveDomain K) := by
  have hOpenProd : IsOpen (C ×ˢ D) := hCopen.prod hDopen
  have hMemProd : (u, v) ∈ C ×ˢ D := ⟨huC, hvD⟩
  have hSubset : C ×ˢ D ⊆ saddleFunctionEffectiveDomain K := by
    intro p hp
    exact hFinite p.1 hp.1 p.2 hp.2
  -- The finite rectangle is an open neighborhood of `(u, v)` contained in the effective domain.
  exact mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (hOpenProd.mem_nhds hMemProd) hSubset

/-- Helper for Theorem 35.8: interior membership in the saddle effective domain yields the finite
open convex rectangle required by Theorem 35.6. -/
lemma helperForTheorem_35_8_finiteRectangle_of_memInterior_effectiveDomain
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (saddleFunctionEffectiveDomain K)) :
    ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
      IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
      IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
          ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal) := by
  -- This is the same interior-to-rectangle bridge isolated earlier for the converse pivot.
  exact
    helperForTheorem_35_8_openConvexFiniteRectangle_of_jointInterior
      (K := K) (u := u) (v := v) hInterior

lemma helperForTheorem_35_8_linear_saddleDirectionalDerivative_of_singleton_partials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFiniteRect :
      ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
        IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
          IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
            ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    ∀ u' v',
      IsSaddleDirectionalDerivativeAt K u v u' v'
        (((((∑ i : Fin m, uStar i * u' i) + ∑ j : Fin n, vStar j * v' j) : ℝ) : EReal)) := by
  classical
  rcases hFiniteRect with ⟨C, D, hCopen, huC, hCconv, hDopen, hvD, hDconv, hFiniteCD⟩
  -- Apply Theorem 35.6 on the finite open convex rectangle to obtain the real directional-derivative
  -- kernel `Kdir` and its splitting formula.
  rcases
      section35_theorem35_6 (C := C) (D := D) (K := K)
        hCopen hDopen hCconv hDconv hK hFiniteCD huC hvD with
    ⟨Kdir, hKdir, _hPos, _hCC, hSplit⟩

  -- Identify the first-axis values `Kdir u' 0` using the singleton support-function formula.
  have hAxisFirst :
      ∀ u' : Fin m → ℝ,
        (Kdir u' 0 : EReal) =
          ((((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) := by
    intro u'
    -- The defining set of directional-derivative values is a singleton because the limit is unique.
    have hSetEq :
        {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
          {(Kdir u' 0 : EReal)} := by
      ext L
      constructor
      · intro hL
        have hEq : L = (Kdir u' 0 : EReal) :=
          tendsto_nhds_unique hL.2.2 (hKdir u' 0).2.2
        simpa [hEq]
      · intro hL
        have hEq : L = (Kdir u' 0 : EReal) := by
          simpa [Set.mem_singleton_iff] using hL
        simpa [hEq] using (hKdir u' 0)
    -- The earlier singleton-axis helper already identifies the raw first-direction derivative set.
    have hFormula :
        sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
          ((((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) :=
      helperForTheorem_35_8_firstAxisDirectionalDerivative_value_of_singleton_partial
        (K := K) (u := u) (v := v) (uStar := uStar) hK hFinite hFirstSingleton u'
    -- Rewrite both sides to singletons and read off the axis value.
    simpa [hSetEq] using hFormula

  -- Identify the second-axis values `Kdir 0 v'` using the singleton support-function formula.
  have hAxisSecond :
      ∀ v' : Fin n → ℝ,
        (Kdir 0 v' : EReal) =
          ((((∑ j : Fin n, vStar j * v' j) : ℝ) : EReal)) := by
    intro v'
    have hSetEq :
        {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
          {(Kdir 0 v' : EReal)} := by
      ext L
      constructor
      · intro hL
        have hEq : L = (Kdir 0 v' : EReal) :=
          tendsto_nhds_unique hL.2.2 (hKdir 0 v').2.2
        simpa [hEq]
      · intro hL
        have hEq : L = (Kdir 0 v' : EReal) := by
          simpa [Set.mem_singleton_iff] using hL
        simpa [hEq] using (hKdir 0 v')
    have hFormula :
        sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
          ((((∑ j : Fin n, vStar j * v' j) : ℝ) : EReal)) :=
      helperForTheorem_35_8_secondAxisDirectionalDerivative_value_of_singleton_partial
        (K := K) (u := u) (v := v) (vStar := vStar) hK hFinite hSecondSingleton v'
    simpa [hSetEq] using hFormula

  -- Convert the axis identifications into real equalities.
  have hAxisFirstReal :
      ∀ u' : Fin m → ℝ, Kdir u' 0 = (∑ i : Fin m, uStar i * u' i) := by
    intro u'
    exact (EReal.coe_eq_coe_iff).1 (hAxisFirst u')
  have hAxisSecondReal :
      ∀ v' : Fin n → ℝ, Kdir 0 v' = (∑ j : Fin n, vStar j * v' j) := by
    intro v'
    exact (EReal.coe_eq_coe_iff).1 (hAxisSecond v')

  -- Finally, use the splitting formula `Kdir u' v' = Kdir u' 0 + Kdir 0 v'` to identify the mixed
  -- values and rewrite the saddle directional-derivative witness.
  intro u' v'
  have hKdirLinear :
      Kdir u' v' =
        (∑ i : Fin m, uStar i * u' i) + (∑ j : Fin n, vStar j * v' j) := by
    calc
      Kdir u' v' = Kdir u' 0 + Kdir 0 v' := hSplit u' v'
      _ = (∑ i : Fin m, uStar i * u' i) + (∑ j : Fin n, vStar j * v' j) := by
        simp [hAxisFirstReal u', hAxisSecondReal v']
  -- The `IsSaddleDirectionalDerivativeAt` witness from Theorem 35.6 now has the desired value.
  simpa [hKdirLinear] using (hKdir u' v')

/-- Helper for Theorem 35.8: on any finite open convex rectangle around `(u, v)`, the real-valued
kernel obtained by taking `toReal` has saddle subdifferential exactly `{(uStar, vStar)}` once the
global singleton partials and the linear mixed directional-derivative formula are available. -/
lemma helperForTheorem_35_8_localRealSingletonSubgradient_onRectangle
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFiniteRect :
      ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
        IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
          IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
            ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar})
    (hLinearDir :
      ∀ u' v',
        IsSaddleDirectionalDerivativeAt K u v u' v'
          (((((∑ i : Fin m, uStar i * u' i) + ∑ j : Fin n, vStar j * v' j) : ℝ) : EReal))) :
    ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
      IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
      IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
        (∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal)) ∧
        let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
        IsRealConcaveConvexOn C D Kloc ∧
          realSaddleSubdifferentialOn C D Kloc u v = {(uStar, vStar)} := by
  classical
  rcases hFiniteRect with ⟨C, D, hCopen, huC, hCconv, hDopen, hvD, hDconv, hFiniteCD⟩
  let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
  let f : (Fin m → ℝ) → EReal :=
    fun x => if x ∈ C then ((-(Kloc x v) : ℝ) : EReal) else (⊤ : EReal)
  let g : (Fin n → ℝ) → EReal :=
    fun y => if y ∈ D then ((Kloc u y : ℝ) : EReal) else (⊤ : EReal)
  have hRealCC : IsRealConcaveConvexOn C D Kloc := by
    -- Convert the finite `EReal` rectangle into a real concave-convex kernel by applying the
    -- Chapter 24 `toReal` bridge slice-by-slice.
    refine ⟨?_, ?_⟩
    · intro y hy
      have hf : ConvexFunction (fun x : Fin m → ℝ => -K x y) := hK.1 y
      have hfFinite :
          ∀ x ∈ C, (fun x : Fin m → ℝ => -K x y) x ≠ (⊤ : EReal) ∧
            (fun x : Fin m → ℝ => -K x y) x ≠ (⊥ : EReal) := by
        intro x hx
        have hxyFinite := hFiniteCD x hx y hy
        exact ⟨by simpa using hxyFinite.2, by simpa using hxyFinite.1⟩
      rcases
          helperForTheorem_5_24_8_toRealConvexOn_and_pointwiseTendsto
            (C := C) (hCconv := hCconv) (f := fun x : Fin m → ℝ => -K x y) hf hfFinite
            (fSeq := fun _ => fun x : Fin m → ℝ => -K x y)
            (hfSeq := fun _ => hf) (hfSeq_finite := fun _ => hfFinite)
            (hpoint := by
              intro x hx
              exact
                (tendsto_const_nhds :
                  Filter.Tendsto (fun _ : ℕ => (-K x y)) Filter.atTop
                    (nhds (-K x y)))) with
        ⟨_hCsubdom, _hCsubdomSeq, hConvToReal, _hConvSeq, _hPointSeq⟩
      have hNegConv : ConvexOn ℝ C (fun x : Fin m → ℝ => -(K x y).toReal) := by
        simpa [Kloc, EReal.toReal_neg] using hConvToReal
      exact (neg_convexOn_iff).1 hNegConv
    · intro x hx
      have hgConv : ConvexFunction (K x) := hK.2 x
      have hgFinite :
          ∀ y ∈ D, K x y ≠ (⊤ : EReal) ∧ K x y ≠ (⊥ : EReal) := by
        intro y hy
        exact hFiniteCD x hx y hy
      rcases
          helperForTheorem_5_24_8_toRealConvexOn_and_pointwiseTendsto
            (C := D) (hCconv := hDconv) (f := K x) hgConv hgFinite
            (fSeq := fun _ => K x) (hfSeq := fun _ => hgConv) (hfSeq_finite := fun _ => hgFinite)
            (hpoint := by
              intro y hy
              exact
                (tendsto_const_nhds :
                  Filter.Tendsto (fun _ : ℕ => K x y) Filter.atTop (nhds (K x y)))) with
        ⟨_hDsubdom, _hDsubdomSeq, hConvToReal, _hConvSeq, _hPointSeq⟩
      simpa [Kloc] using hConvToReal
  have hBridge :
      (∀ u0 : Fin m → ℝ,
          u0 ∈ realPartialSubdifferentialInFirstVariableOn C Kloc u v ↔
            dotProductEquiv ℝ (Fin m) (-u0) ∈ subdifferentialAt f u) ∧
        (∀ v0 : Fin n → ℝ,
          v0 ∈ realPartialSubdifferentialInSecondVariableOn D Kloc u v ↔
            dotProductEquiv ℝ (Fin n) v0 ∈ subdifferentialAt g v) := by
    -- The local real partials are exactly the Chapter 23 subdifferentials of the `⊤`-extensions.
    simpa [f, g] using
      helperForTheorem_35_7_realPartialSubdifferential_bridges
        (C := C) (D := D) (K := Kloc) (u := u) (v := v) huC hvD
  have hRealFirstDir :
      ∀ u' : Fin m → ℝ,
        HasRealSaddleDirectionalDerivativeAt Kloc u v u' 0
          (∑ i : Fin m, uStar i * u' i) := by
    intro u'
    have hBaseFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFiniteCD u huC v hvD
    have hDirE := hLinearDir u' 0
    have hcontWithin :
        ContinuousWithinAt (fun t : ℝ => u + t • u') (Set.Ioi (0 : ℝ)) (0 : ℝ) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt
    have htend :
        Filter.Tendsto (fun t : ℝ => u + t • u')
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds u) := by
      have hMaps :
          Set.MapsTo (fun t : ℝ => u + t • u') (Set.Ioi (0 : ℝ))
            (Set.univ : Set (Fin m → ℝ)) := by
        intro t ht
        trivial
      simpa using (hcontWithin.tendsto_nhdsWithin hMaps)
    have hmemC : ∀ᶠ t in (𝓝[>] (0 : ℝ)), u + t • u' ∈ C :=
      htend.eventually (hCopen.mem_nhds huC)
    have htpos : ∀ᶠ t in (𝓝[>] (0 : ℝ)), t ∈ Set.Ioi (0 : ℝ) := by
      simpa [Filter.Eventually] using
        (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
    have hquot_event :
        saddleDirectionalDifferenceQuotientAt K u v u' 0 =ᶠ[(𝓝[>] (0 : ℝ))]
          fun t : ℝ =>
            ((realSaddleDirectionalDifferenceQuotientAt Kloc u v u' 0 t : ℝ) : EReal) := by
      filter_upwards [hmemC, htpos] with t htC htpos
      have htne : (t : ℝ) ≠ 0 := ne_of_gt (Set.mem_Ioi.mp htpos)
      have hStepFinite : K (u + t • u') v ≠ (⊤ : EReal) ∧ K (u + t • u') v ≠ (⊥ : EReal) :=
        by
          simpa [Pi.add_apply, Pi.smul_apply] using
            hFiniteCD (u + t • u') htC v hvD
      have hStepCoe :
          K (u + t • u') v = (((Kloc (u + t • u') v : ℝ)) : EReal) := by
        symm
        exact EReal.coe_toReal hStepFinite.1 hStepFinite.2
      have hBaseCoe : K u v = (((Kloc u v : ℝ)) : EReal) := by
        symm
        exact EReal.coe_toReal hBaseFinite.1 hBaseFinite.2
      calc
        saddleDirectionalDifferenceQuotientAt K u v u' 0 t
            = (K (u + t • u') (v + t • (0 : Fin n → ℝ)) - K u v) / (t : EReal) := by
                simp [saddleDirectionalDifferenceQuotientAt]
        _ = ((((Kloc (u + t • u') v : ℝ) : EReal) - ((Kloc u v : ℝ) : EReal)) / (t : EReal)) := by
              simp [hStepCoe, hBaseCoe]
        _ = ((((Kloc (u + t • u') v - Kloc u v) / t : ℝ)) : EReal) := by
              rw [← EReal.coe_sub (Kloc (u + t • u') v) (Kloc u v)]
              rw [← EReal.coe_div (Kloc (u + t • u') v - Kloc u v) t]
        _ = ((realSaddleDirectionalDifferenceQuotientAt Kloc u v u' 0 t : ℝ) : EReal) := by
              simp [realSaddleDirectionalDifferenceQuotientAt]
    have hTendstoE :
        Filter.Tendsto
          (fun t : ℝ => ((realSaddleDirectionalDifferenceQuotientAt Kloc u v u' 0 t : ℝ) : EReal))
          (𝓝[>] (0 : ℝ))
          (nhds (((((∑ i : Fin m, uStar i * u' i) + ∑ j : Fin n, vStar j * (0 : Fin n → ℝ) j) :
            ℝ) : ℝ) : EReal)) := by
      exact Filter.Tendsto.congr' hquot_event hDirE.2.2
    -- On the first axis, the mixed linear value collapses to the `uStar` pairing.
    simpa using (EReal.tendsto_coe.1 hTendstoE)
  have hRealSecondDir :
      ∀ v' : Fin n → ℝ,
        HasRealSaddleDirectionalDerivativeAt Kloc u v 0 v'
          (∑ j : Fin n, vStar j * v' j) := by
    intro v'
    have hBaseFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFiniteCD u huC v hvD
    have hDirE := hLinearDir 0 v'
    have hcontWithin :
        ContinuousWithinAt (fun t : ℝ => v + t • v') (Set.Ioi (0 : ℝ)) (0 : ℝ) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt
    have htend :
        Filter.Tendsto (fun t : ℝ => v + t • v')
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds v) := by
      have hMaps :
          Set.MapsTo (fun t : ℝ => v + t • v') (Set.Ioi (0 : ℝ))
            (Set.univ : Set (Fin n → ℝ)) := by
        intro t ht
        trivial
      simpa using (hcontWithin.tendsto_nhdsWithin hMaps)
    have hmemD : ∀ᶠ t in (𝓝[>] (0 : ℝ)), v + t • v' ∈ D :=
      htend.eventually (hDopen.mem_nhds hvD)
    have htpos : ∀ᶠ t in (𝓝[>] (0 : ℝ)), t ∈ Set.Ioi (0 : ℝ) := by
      simpa [Filter.Eventually] using
        (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
    have hquot_event :
        saddleDirectionalDifferenceQuotientAt K u v 0 v' =ᶠ[(𝓝[>] (0 : ℝ))]
          fun t : ℝ =>
            ((realSaddleDirectionalDifferenceQuotientAt Kloc u v 0 v' t : ℝ) : EReal) := by
      filter_upwards [hmemD, htpos] with t htD htpos
      have htne : (t : ℝ) ≠ 0 := ne_of_gt (Set.mem_Ioi.mp htpos)
      have hStepFinite : K u (v + t • v') ≠ (⊤ : EReal) ∧ K u (v + t • v') ≠ (⊥ : EReal) :=
        by
          simpa [Pi.add_apply, Pi.smul_apply] using
            hFiniteCD u huC (v + t • v') htD
      have hStepCoe :
          K u (v + t • v') = (((Kloc u (v + t • v') : ℝ)) : EReal) := by
        symm
        exact EReal.coe_toReal hStepFinite.1 hStepFinite.2
      have hBaseCoe : K u v = (((Kloc u v : ℝ)) : EReal) := by
        symm
        exact EReal.coe_toReal hBaseFinite.1 hBaseFinite.2
      calc
        saddleDirectionalDifferenceQuotientAt K u v 0 v' t
            = (K (u + t • (0 : Fin m → ℝ)) (v + t • v') - K u v) / (t : EReal) := by
                simp [saddleDirectionalDifferenceQuotientAt]
        _ = ((((Kloc u (v + t • v') : ℝ) : EReal) - ((Kloc u v : ℝ) : EReal)) / (t : EReal)) := by
              simp [hStepCoe, hBaseCoe]
        _ = ((((Kloc u (v + t • v') - Kloc u v) / t : ℝ)) : EReal) := by
              rw [← EReal.coe_sub (Kloc u (v + t • v')) (Kloc u v)]
              rw [← EReal.coe_div (Kloc u (v + t • v') - Kloc u v) t]
        _ = ((realSaddleDirectionalDifferenceQuotientAt Kloc u v 0 v' t : ℝ) : EReal) := by
              simp [realSaddleDirectionalDifferenceQuotientAt]
    have hTendstoE :
        Filter.Tendsto
          (fun t : ℝ => ((realSaddleDirectionalDifferenceQuotientAt Kloc u v 0 v' t : ℝ) : EReal))
          (𝓝[>] (0 : ℝ))
          (nhds (((((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) + ∑ j : Fin n, vStar j * v' j) :
            ℝ) : ℝ) : EReal)) := by
      exact Filter.Tendsto.congr' hquot_event hDirE.2.2
    -- On the second axis, the first sum vanishes and only the `vStar` pairing remains.
    simpa using (EReal.tendsto_coe.1 hTendstoE)
  have hRealFirstValue :
      ∀ u' : Fin m → ℝ,
        realFirstVariableDirectionalDerivativeValue Kloc u v u' =
          ∑ i : Fin m, uStar i * u' i := by
    intro u'
    have hHas := hRealFirstDir u'
    have hUnique :
        ∀ {L1 L2 : ℝ},
          HasRealSaddleDirectionalDerivativeAt Kloc u v u' 0 L1 →
            HasRealSaddleDirectionalDerivativeAt Kloc u v u' 0 L2 → L1 = L2 := by
      intro L1 L2 h1 h2
      exact tendsto_nhds_unique h1 h2
    have hSetEq :
        {L : ℝ | HasRealSaddleDirectionalDerivativeAt Kloc u v u' 0 L} =
          ({∑ i : Fin m, uStar i * u' i} : Set ℝ) := by
      ext L
      constructor
      · intro hL
        have : L = ∑ i : Fin m, uStar i * u' i := hUnique hL hHas
        simpa [this]
      · intro hL
        have : L = ∑ i : Fin m, uStar i * u' i := by simpa using hL
        simpa [this] using hHas
    simp [realFirstVariableDirectionalDerivativeValue, hSetEq]
  have hRealSecondValue :
      ∀ v' : Fin n → ℝ,
        realSecondVariableDirectionalDerivativeValue Kloc u v v' =
          ∑ j : Fin n, vStar j * v' j := by
    intro v'
    have hHas := hRealSecondDir v'
    have hUnique :
        ∀ {L1 L2 : ℝ},
          HasRealSaddleDirectionalDerivativeAt Kloc u v 0 v' L1 →
            HasRealSaddleDirectionalDerivativeAt Kloc u v 0 v' L2 → L1 = L2 := by
      intro L1 L2 h1 h2
      exact tendsto_nhds_unique h1 h2
    have hSetEq :
        {L : ℝ | HasRealSaddleDirectionalDerivativeAt Kloc u v 0 v' L} =
          ({∑ j : Fin n, vStar j * v' j} : Set ℝ) := by
      ext L
      constructor
      · intro hL
        have : L = ∑ j : Fin n, vStar j * v' j := hUnique hL hHas
        simpa [this]
      · intro hL
        have : L = ∑ j : Fin n, vStar j * v' j := by simpa using hL
        simpa [this] using hHas
    simp [realSecondVariableDirectionalDerivativeValue, hSetEq]
  have hfConvOn : ConvexOn ℝ C (fun x : Fin m → ℝ => -(Kloc x v)) := (hRealCC.1 v hvD).neg
  have hgConvOn : ConvexOn ℝ D (fun y : Fin n → ℝ => Kloc u y) := hRealCC.2 u huC
  have hfExt :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := C) (f := fun x : Fin m → ℝ => -(Kloc x v)) hfConvOn
  have hgExt :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := D) (f := fun y : Fin n → ℝ => Kloc u y) hgConvOn
  have hfConv : ConvexFunction f := by
    simpa [f] using hfExt.1
  have hgConv : ConvexFunction g := by
    simpa [g] using hgExt.1
  have hfu : f u ≠ (⊤ : EReal) ∧ f u ≠ (⊥ : EReal) := by
    simpa [f] using hfExt.2 u huC
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    simpa [g] using hgExt.2 v hvD
  have hFirstUpper :
      ∀ u' : Fin m → ℝ,
        upperDirectionalDerivativeAt f u u' =
          ((((dotProduct (-uStar) u' : ℝ) : ℝ) : EReal)) := by
    intro u'
    have hBridgeDir :=
      helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
        (C := C) (D := D) (K := Kloc) hCopen hDopen hCconv hDconv hRealCC huC hvD u' 0
    have hEq :
        ((((∑ i : Fin m, uStar i * u' i) : ℝ) : ℝ) : EReal) =
          -upperDirectionalDerivativeAt f u u' := by
      simpa [f, g, hRealFirstValue u'] using hBridgeDir.1
    have hEq' :
        upperDirectionalDerivativeAt f u u' =
          -(((((∑ i : Fin m, uStar i * u' i) : ℝ) : ℝ) : EReal)) := by
      have hTmp :
          -(((((∑ i : Fin m, uStar i * u' i) : ℝ) : ℝ) : EReal)) =
            upperDirectionalDerivativeAt f u u' := by
        simpa using congrArg Neg.neg hEq
      exact hTmp.symm
    simpa [dotProduct_neg] using hEq'
  have hSecondUpper :
      ∀ v' : Fin n → ℝ,
        upperDirectionalDerivativeAt g v v' =
          ((((dotProduct vStar v' : ℝ) : ℝ) : EReal)) := by
    intro v'
    have hBridgeDir :=
      helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
        (C := C) (D := D) (K := Kloc) hCopen hDopen hCconv hDconv hRealCC huC hvD 0 v'
    have hTmp :
        ((((dotProduct vStar v' : ℝ) : ℝ) : EReal)) =
          upperDirectionalDerivativeAt g v v' := by
      simpa [f, g, hRealSecondValue v'] using hBridgeDir.2
    exact hTmp.symm
  have hSubFirstTarget :
      IsSubgradientAt f u (dotProductEquiv ℝ (Fin m) (-uStar)) := by
    -- The first-axis directional derivative formula produces the target subgradient directly.
    have hiff :=
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hfConv u hfu (dotProductEquiv ℝ (Fin m) (-uStar))).1
    apply hiff.mpr
    intro y
    simpa [hFirstUpper y]
  have hSubSecondTarget :
      IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) vStar) := by
    -- The same Chapter 23 characterization applies to the second-variable extension.
    have hiff :=
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hgConv v hgv (dotProductEquiv ℝ (Fin n) vStar)).1
    apply hiff.mpr
    intro y
    simpa [hSecondUpper y]
  have huniqFirst :
      ∃! w : Fin m → ℝ, IsSubgradientAt f u (dotProductEquiv ℝ (Fin m) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := f) (hf := hfConv) (x := u) (hx := hfu) (g := -uStar) hFirstUpper
  have huniqSecond :
      ∃! w : Fin n → ℝ, IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := g) (hf := hgConv) (x := v) (hx := hgv) (g := vStar) hSecondUpper
  have hFirstLocalSingleton :
      realPartialSubdifferentialInFirstVariableOn C Kloc u v = {uStar} := by
    rcases huniqFirst with ⟨w0, _hw0, hwuniq⟩
    have hw0Eq : w0 = -uStar := by
      exact (hwuniq (-uStar) hSubFirstTarget).symm
    ext w
    constructor
    · intro hw
      have hwSub :
          IsSubgradientAt f u (dotProductEquiv ℝ (Fin m) (-w)) := by
        have : dotProductEquiv ℝ (Fin m) (-w) ∈ subdifferentialAt f u := (hBridge.1 w).1 hw
        simpa [subdifferentialAt] using this
      have hEqNeg : -w = w0 := hwuniq (-w) hwSub
      have hEqNeg' : -w = -uStar := by simpa [hw0Eq] using hEqNeg
      have hEq : w = uStar := by
        simpa using congrArg Neg.neg hEqNeg'
      simpa [hEq]
    · intro hw
      have hwEq : w = uStar := by simpa using hw
      have : dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt f u := by
        simpa [subdifferentialAt] using hSubFirstTarget
      simpa [hwEq] using (hBridge.1 uStar).2 this
  have hSecondLocalSingleton :
      realPartialSubdifferentialInSecondVariableOn D Kloc u v = {vStar} := by
    rcases huniqSecond with ⟨w0, _hw0, hwuniq⟩
    have hw0Eq : w0 = vStar := by
      exact (hwuniq vStar hSubSecondTarget).symm
    ext w
    constructor
    · intro hw
      have hwSub :
          IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) w) := by
        have : dotProductEquiv ℝ (Fin n) w ∈ subdifferentialAt g v := (hBridge.2 w).1 hw
        simpa [subdifferentialAt] using this
      have hEq : w = w0 := hwuniq w hwSub
      simpa [hw0Eq] using hEq
    · intro hw
      have hwEq : w = vStar := by simpa using hw
      have : dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt g v := by
        simpa [subdifferentialAt] using hSubSecondTarget
      simpa [hwEq] using (hBridge.2 vStar).2 this
  refine ⟨C, D, hCopen, huC, hCconv, hDopen, hvD, hDconv, hFiniteCD, ?_⟩
  -- With the axis subgradients pinned down uniquely, the local product saddle subdifferential is
  -- exactly the singleton pair.
  refine ⟨hRealCC, ?_⟩
  ext p
  constructor
  · intro hp
    have hp' :
        p.1 ∈ realPartialSubdifferentialInFirstVariableOn C Kloc u v ∧
          p.2 ∈ realPartialSubdifferentialInSecondVariableOn D Kloc u v := by
      simpa [realSaddleSubdifferentialOn] using hp
    have hp1 : p.1 = uStar := by
      simpa [hFirstLocalSingleton] using hp'.1
    have hp2 : p.2 = vStar := by
      simpa [hSecondLocalSingleton] using hp'.2
    exact Prod.ext hp1 hp2
  · intro hp
    rcases hp with rfl
    have huMem : uStar ∈ realPartialSubdifferentialInFirstVariableOn C Kloc u v := by
      simpa [hFirstLocalSingleton]
    have hvMem : vStar ∈ realPartialSubdifferentialInSecondVariableOn D Kloc u v := by
      simpa [hSecondLocalSingleton]
    exact by simpa [realSaddleSubdifferentialOn] using And.intro huMem hvMem

/-- Helper for Theorem 35.8: the `ℓ¹`/`ℓ∞` estimate controls the absolute value of a dot product. -/
lemma helperForTheorem_35_8_abs_dotProduct_le_l1Norm_mul_norm
    {k : ℕ} (a b : Fin k → ℝ) :
    |dotProduct a b| ≤ l1Norm a * ‖b‖ := by
  -- Bound the positive side directly and the negative side by applying the same estimate to `-a`.
  have hUpper :
      dotProduct a b ≤ l1Norm a * ‖b‖ :=
    section13_dotProduct_le_l1Norm_mul_norm (n := k) a b
  have hLower :
      -dotProduct a b ≤ l1Norm a * ‖b‖ := by
    simpa [dotProduct_neg, l1Norm, Finset.sum_nonneg, norm_neg] using
      (section13_dotProduct_le_l1Norm_mul_norm (n := k) (-a) b)
  exact abs_le.2 ⟨by linarith, hUpper⟩

/-- Helper for Theorem 35.8: the first block of a packed vector has norm bounded by the packed
norm. -/
lemma helperForTheorem_35_8_norm_le_norm_append_left
    {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) :
    ‖a‖ ≤ ‖Fin.append a b‖ := by
  -- Each coordinate of the first block is one coordinate of the packed vector.
  refine (pi_norm_le_iff_of_nonneg (x := a) (r := ‖Fin.append a b‖) (norm_nonneg _)).2 ?_
  intro i
  simpa [Fin.append] using
    (norm_le_pi_norm (f := Fin.append a b) (i := Fin.castAdd n i))

/-- Helper for Theorem 35.8: the second block of a packed vector has norm bounded by the packed
norm. -/
lemma helperForTheorem_35_8_norm_le_norm_append_right
    {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) :
    ‖b‖ ≤ ‖Fin.append a b‖ := by
  -- The same coordinatewise estimate works for the second block.
  refine (pi_norm_le_iff_of_nonneg (x := b) (r := ‖Fin.append a b‖) (norm_nonneg _)).2 ?_
  intro j
  simpa [Fin.append] using
    (norm_le_pi_norm (f := Fin.append a b) (i := Fin.natAdd m j))

/-- Helper for Theorem 35.8: on `Fin k → ℝ`, the `ℓ¹` norm is bounded by the dimension times the
sup norm. -/
lemma helperForTheorem_35_8_l1Norm_le_card_mul_norm
    {k : ℕ} (x : Fin k → ℝ) :
    l1Norm x ≤ (k : ℝ) * ‖x‖ := by
  -- Sum the coordinatewise sup-norm bounds over the `k` coordinates.
  unfold l1Norm
  have hcoord : ∀ i : Fin k, ‖x i‖ ≤ ‖x‖ := by
    intro i
    exact norm_le_pi_norm x i
  have hsum :
      (∑ i : Fin k, ‖x i‖) ≤ ∑ _i : Fin k, ‖x‖ := by
    exact Finset.sum_le_sum (fun i _ => hcoord i)
  simpa [Finset.sum_const_nat, nsmul_eq_mul] using hsum

/-- Helper for Theorem 35.8: every interior point of the finite open rectangle has a nonempty real
saddle subdifferential. -/
lemma helperForTheorem_35_8_nonempty_realSaddleSubdifferentialOn_of_mem_openRectangle
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hCopen : IsOpen C) (hDopen : IsOpen D)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    {x : Fin m → ℝ} {y : Fin n → ℝ}
    (hx : x ∈ C) (hy : y ∈ D) :
    Set.Nonempty (realSaddleSubdifferentialOn C D K x y) := by
  classical
  let f : (Fin m → ℝ) → EReal :=
    fun z => if z ∈ C then ((-(K z y) : ℝ) : EReal) else (⊤ : EReal)
  let g : (Fin n → ℝ) → EReal :=
    fun z => if z ∈ D then ((K x z : ℝ) : EReal) else (⊤ : EReal)
  have hfExt :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := C) (f := fun z : Fin m → ℝ => -(K z y)) ((hK.1 y hy).neg)
  have hgExt :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := D) (f := fun z : Fin n → ℝ => K x z) (hK.2 x hx)
  have hEffF :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) f = C := by
    ext z
    by_cases hz : z ∈ C
    · simp [f, hz, effectiveDomain_eq, lt_top_iff_ne_top]
    · simp [f, hz, effectiveDomain_eq, lt_top_iff_ne_top]
  have hEffG :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) g = D := by
    ext z
    by_cases hz : z ∈ D
    · simp [g, hz, effectiveDomain_eq, lt_top_iff_ne_top]
    · simp [g, hz, effectiveDomain_eq, lt_top_iff_ne_top]
  have hxInt :
      x ∈ interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) := by
    rw [hEffF, hCopen.interior_eq]
    exact hx
  have hyInt :
      y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
    rw [hEffG, hDopen.interior_eq]
    exact hy
  have hfxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    simpa [f] using hfExt.2 x hx
  have hgyFinite : g y ≠ (⊤ : EReal) ∧ g y ≠ (⊥ : EReal) := by
    simpa [g] using hgExt.2 y hy
  have hProperF :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f :=
    helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
      hfExt.1 hxInt hfxFinite.2
  have hProperG :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
      hgExt.1 hyInt hgyFinite.2
  have h23F :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      f hProperF x
  have h23G :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      g hProperG y
  have hSubF :
      Set.Nonempty (subdifferentialAt f x) :=
    ((h23F.2.2.1).2 hxInt).1
  have hSubG :
      Set.Nonempty (subdifferentialAt g y) :=
    ((h23G.2.2.1).2 hyInt).1
  have hBridge :=
    helperForTheorem_35_7_realPartialSubdifferential_bridges
      (C := C) (D := D) (K := K) (u := x) (v := y) hx hy
  rcases hSubF with ⟨xf, hxf⟩
  rcases hSubG with ⟨yg, hyg⟩
  let p : Fin m → ℝ := -((dotProductEquiv ℝ (Fin m)).symm xf)
  let q : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm yg
  have hp :
      p ∈ realPartialSubdifferentialInFirstVariableOn C K x y := by
    exact (hBridge.1 p).2 (by simpa [p] using hxf)
  have hq :
      q ∈ realPartialSubdifferentialInSecondVariableOn D K x y := by
    exact (hBridge.2 q).2 (by simpa [q] using hyg)
  refine ⟨(p, q), ?_⟩
  simpa [realSaddleSubdifferentialOn] using And.intro hp hq

/-- Helper for Theorem 35.8: on a finite open rectangle, Corollary 35.7.1 upgrades a singleton
base saddle subgradient into split-ball control of every nearby saddle subgradient. -/
lemma helperForTheorem_35_8_nearbyRealSubgradient_close_to_singleton
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hCopen : IsOpen C) (huC : u ∈ C) (hCconv : Convex ℝ C)
    (hDopen : IsOpen D) (hvD : v ∈ D) (hDconv : Convex ℝ D)
    (hRealCC : IsRealConcaveConvexOn C D Kloc)
    (hLocal : realSaddleSubdifferentialOn C D Kloc u v = {(uStar, vStar)}) :
    ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ x : Fin m → ℝ, x ∈ C → ∀ y : Fin n → ℝ, y ∈ D →
          ((x - u), (y - v)) ∈ splitEuclideanClosedBall (m := m) (n := n) δ →
            ∀ ⦃p : Fin m → ℝ⦄ ⦃q : Fin n → ℝ⦄,
              (p, q) ∈ realSaddleSubdifferentialOn C D Kloc x y →
                ((p - uStar), (q - vStar)) ∈
                  splitEuclideanClosedBall (m := m) (n := n) η := by
  intro η hη
  rcases
      (section35_corollary35_7_1
        (C := C) (D := D) (K := Kloc) hCopen hDopen hCconv hDconv hRealCC).2.2
        huC hvD η hη with
    ⟨δ, hδ, hδclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy p q hpq
  have hpImage :=
    hδclose x hx y hy hxy hpq
  rcases (by simpa [Set.mem_image2] using hpImage) with
    ⟨base, hbase, err, herr, hsum⟩
  have hbaseEq : base = (uStar, vStar) := by
    simpa [hLocal] using hbase
  rcases err with ⟨du, dv⟩
  have hsum' : (uStar + du, vStar + dv) = (p, q) := by
    simpa [hbaseEq] using hsum
  have hpEq : uStar + du = p := by
    exact congrArg Prod.fst hsum'
  have hqEq : vStar + dv = q := by
    exact congrArg Prod.snd hsum'
  have hduEq : du = p - uStar := by
    funext i
    have hi : uStar i + du i = p i := by
      simpa using congrArg (fun w : Fin m → ℝ => w i) hpEq
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hi)
  have hdvEq : dv = q - vStar := by
    funext j
    have hj : vStar j + dv j = q j := by
      simpa using congrArg (fun w : Fin n → ℝ => w j) hqEq
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hj)
  -- The nearby subgradient differs from the singleton base witness by exactly the split-ball
  -- error term supplied by Corollary 35.7.1.
  simpa [hduEq, hdvEq] using herr

/-- Helper for Theorem 35.8: once a nearby local saddle subgradient `(p, q)` is chosen, the
subgradient inequalities sandwich the packed real remainder by explicit `ℓ¹`/`ℓ∞` errors. -/
lemma helperForTheorem_35_8_packedRealErrorBound_of_nearbySingletonSubgradients
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (huC : u ∈ C) (hvD : v ∈ D)
    (hBase :
      realSaddleSubdifferentialOn C D Kloc u v = {(uStar, vStar)})
    {x : Fin m → ℝ} {y : Fin n → ℝ}
    (hxC : x ∈ C) (hyD : y ∈ D)
    {p : Fin m → ℝ} {q : Fin n → ℝ}
    (hNear : (p, q) ∈ realSaddleSubdifferentialOn C D Kloc x y) :
    |Kloc x y - Kloc u v -
        (dotProduct uStar (x - u) + dotProduct vStar (y - v))| ≤
      (l1Norm (uStar - p) + l1Norm (q - vStar)) *
        ‖Fin.append (x - u) (y - v)‖ := by
  have hBaseMem : (uStar, vStar) ∈ realSaddleSubdifferentialOn C D Kloc u v := by
    simpa [hBase]
  have hBaseParts :
      uStar ∈ realPartialSubdifferentialInFirstVariableOn C Kloc u v ∧
        vStar ∈ realPartialSubdifferentialInSecondVariableOn D Kloc u v := by
    simpa [realSaddleSubdifferentialOn] using hBaseMem
  have hNearParts :
      p ∈ realPartialSubdifferentialInFirstVariableOn C Kloc x y ∧
        q ∈ realPartialSubdifferentialInSecondVariableOn D Kloc x y := by
    simpa [realSaddleSubdifferentialOn] using hNear
  let dx : Fin m → ℝ := x - u
  let dy : Fin n → ℝ := y - v
  let dz : Fin (m + n) → ℝ := Fin.append dx dy
  let err : ℝ :=
    Kloc x y - Kloc u v - (dotProduct uStar dx + dotProduct vStar dy)
  have hBaseFirst :
      Kloc x v ≤ Kloc u v + dotProduct uStar dx := by
    simpa [dx, dotProduct, sub_eq_add_neg] using hBaseParts.1 x hxC
  have hBaseSecond :
      Kloc u y ≥ Kloc u v + dotProduct vStar dy := by
    simpa [dy, dotProduct, sub_eq_add_neg] using hBaseParts.2 y hyD
  have hNearFirst :
      Kloc u y ≤ Kloc x y - dotProduct p dx := by
    have hNearFirstRaw :
        Kloc u y ≤ Kloc x y + dotProduct p (u - x) := by
      simpa [dotProduct, sub_eq_add_neg] using hNearParts.1 u huC
    have hEq : dotProduct p (u - x) = -dotProduct p dx := by
      rw [show u - x = -dx by simp [dx]]
      simp [dotProduct_neg]
    rw [hEq] at hNearFirstRaw
    linarith
  have hNearSecond :
      Kloc x v ≥ Kloc x y - dotProduct q dy := by
    have hNearSecondRaw :
        Kloc x v ≥ Kloc x y + dotProduct q (v - y) := by
      simpa [dotProduct, sub_eq_add_neg] using hNearParts.2 v hvD
    have hEq : dotProduct q (v - y) = -dotProduct q dy := by
      rw [show v - y = -dy by simp [dy]]
      simp [dotProduct_neg]
    rw [hEq] at hNearSecondRaw
    linarith
  have hUpper :
      err ≤ dotProduct (q - vStar) dy := by
    -- Compare the base first-variable subgradient at `(u, v)` with the nearby second-variable
    -- subgradient at `(x, y)`.
    have hUpperRaw :
        err ≤ dotProduct q dy - dotProduct vStar dy := by
      dsimp [err, dx, dy]
      linarith
    simpa [dotProduct_sub] using hUpperRaw
  have hNeg :
      -err ≤ dotProduct (uStar - p) dx := by
    -- The opposite comparison uses the nearby first-variable subgradient and the base second one.
    have hNegRaw :
        -err ≤ dotProduct uStar dx - dotProduct p dx := by
      dsimp [err, dx, dy]
      linarith
    simpa [dotProduct_sub] using hNegRaw
  have hBoundUpper :
      dotProduct (q - vStar) dy ≤
        l1Norm (q - vStar) * ‖dz‖ := by
    have h0 :=
      helperForTheorem_35_8_abs_dotProduct_le_l1Norm_mul_norm (q - vStar) dy
    have hNorm :
        ‖dy‖ ≤ ‖dz‖ :=
      helperForTheorem_35_8_norm_le_norm_append_right dx dy
    have hl1_nonneg : 0 ≤ l1Norm (q - vStar) := by
      unfold l1Norm
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    exact le_trans (le_abs_self _) <|
      le_trans h0 (mul_le_mul_of_nonneg_left hNorm hl1_nonneg)
  have hBoundNeg :
      dotProduct (uStar - p) dx ≤
        l1Norm (uStar - p) * ‖dz‖ := by
    have h0 :=
      helperForTheorem_35_8_abs_dotProduct_le_l1Norm_mul_norm (uStar - p) dx
    have hNorm :
        ‖dx‖ ≤ ‖dz‖ :=
      helperForTheorem_35_8_norm_le_norm_append_left dx dy
    have hl1_nonneg : 0 ≤ l1Norm (uStar - p) := by
      unfold l1Norm
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    exact le_trans (le_abs_self _) <|
      le_trans h0 (mul_le_mul_of_nonneg_left hNorm hl1_nonneg)
  have hAbs :
      |err| ≤
        l1Norm (uStar - p) * ‖dz‖ + l1Norm (q - vStar) * ‖dz‖ := by
    have hErrUpper :
        err ≤ l1Norm (q - vStar) * ‖dz‖ :=
      le_trans hUpper hBoundUpper
    have hErrLower :
        -(l1Norm (uStar - p) * ‖dz‖) ≤ err := by
      have : -err ≤ l1Norm (uStar - p) * ‖dz‖ :=
        le_trans hNeg hBoundNeg
      linarith
    have hUpperNonneg : 0 ≤ l1Norm (q - vStar) * ‖dz‖ := by
      unfold l1Norm
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)
    have hLowerNonneg : 0 ≤ l1Norm (uStar - p) * ‖dz‖ := by
      unfold l1Norm
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)
    exact abs_le.2 ⟨by
      linarith, by
      linarith⟩
  have hRepack :
      l1Norm (uStar - p) * ‖dz‖ + l1Norm (q - vStar) * ‖dz‖ =
        (l1Norm (uStar - p) + l1Norm (q - vStar)) * ‖dz‖ := by
    ring
  simpa [err, dx, dy, dz] using hAbs.trans_eq hRepack



end Section35
end Chap07
