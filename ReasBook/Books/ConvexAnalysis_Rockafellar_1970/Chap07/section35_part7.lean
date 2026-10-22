/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part6

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

-- Proof sketch: use the global saddle hypothesis on `K` to obtain the one-variable convexity
-- and concavity properties on all of `ℝ^m × ℝ^n`, then restrict to the open convex set `C × D`
-- where `K` is finite so that `EReal.toReal` is available. Apply the one-variable
-- directional-derivative existence results in the `u`- and `v`-variables at `(u, v)`, and
-- combine these slice derivatives to obtain a real-valued kernel on all directions. Its positive
-- homogeneity, concave-convexity, and splitting formula come from the corresponding properties
-- of directional derivatives of saddle functions.
/-- Theorem 35.6: if `K` is a globally concave-convex extended-real-valued saddle function on
`ℝ^m × ℝ^n`, and if `C × D ⊆ ℝ^m × ℝ^n` is an open convex product on which `K` is finite, then
for each `(u, v) ∈ C × D` there is a finite directional-derivative kernel `Kdir` on
`ℝ^m × ℝ^n` such that `K'(u, v; u', v') = Kdir u' v'` for every direction, `Kdir` is positively
homogeneous and concave-convex on all of `ℝ^m × ℝ^n`, and
`Kdir u' v' = Kdir u' 0 + Kdir 0 v'`. -/
theorem section35_theorem35_6
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    ∃ Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ,
      (∀ u' v', IsSaddleDirectionalDerivativeAt K u v u' v' (Kdir u' v' : EReal)) ∧
      IsPositivelyHomogeneousSaddleKernel Kdir ∧
      IsRealConcaveConvexOn (Set.univ : Set (Fin m → ℝ))
        (Set.univ : Set (Fin n → ℝ)) Kdir ∧
      ∀ u' v', Kdir u' v' = Kdir u' 0 + Kdir 0 v' := by
  -- First package the translated direction domains needed for the compactness step.
  let CU : Set (Fin m → ℝ) := {u' | u + u' ∈ C}
  let DV : Set (Fin n → ℝ) := {v' | v + v' ∈ D}
  obtain ⟨hCU, hDV, h0CU, h0DV, hScaledMem⟩ :=
    helperForTheorem_35_6_translatedDirectionDomains
      (C := C) (D := D) hC_open hD_open hC_conv hD_conv hu hv
  rcases
      helperForTheorem_35_6_splitKernel_structure
        (C := C) (D := D) (K := K)
        hC_open hD_open hC_conv hD_conv hK hFinite hu hv with
    ⟨Kdir, hKdir_formula, hKdir_pos, hKdir_cc, hKdir_split⟩
  have hAxisDir :=
    helperForTheorem_35_6_axisDirectionalDerivatives_match_splitKernel
      (C := C) (D := D) (K := K)
      hC_open hD_open hK hFinite hu hv hKdir_formula
  refine ⟨Kdir, ?_, hKdir_pos, hKdir_cc, hKdir_split⟩
  intro u' v'
  have huC : (0 : Fin m → ℝ) ∈ CU := h0CU
  have hvD : (0 : Fin n → ℝ) ∈ DV := h0DV
  -- The translated domains already record the short-step admissibility needed later.
  have hStepBase :
      ∀ {t : ℝ}, 0 < t → t ≤ 1 →
        u + t • (0 : Fin m → ℝ) ∈ C ∧ v + t • (0 : Fin n → ℝ) ∈ D := by
    intro t ht_pos ht_le
    exact hScaledMem ht_pos ht_le huC hvD
  -- Route correction: the previous proof attempt bundled domain geometry with subsequential-limit
  -- identification. The domain package is now explicit, so the only remaining work is the
  -- compactness/uniqueness argument for the mixed quotient family on `CU × DV`.
  have hAxisFirst : ∀ u'', IsSaddleDirectionalDerivativeAt K u v u'' 0 (Kdir u'' 0 : EReal) :=
    hAxisDir.1
  have hAxisSecond : ∀ v'', IsSaddleDirectionalDerivativeAt K u v 0 v'' (Kdir 0 v'' : EReal) :=
    hAxisDir.2
  have hScaledFinite :
      ∀ {t : ℝ}, 0 < t → t ≤ 1 →
        ∀ {u'' : Fin m → ℝ} {v'' : Fin n → ℝ}, u'' ∈ CU → v'' ∈ DV →
          K (u + t • u'') (v + t • v'') ≠ (⊤ : EReal) ∧
            K (u + t • u'') (v + t • v'') ≠ (⊥ : EReal) :=
    by
      intro t ht_pos ht_le u'' v'' hu'' hv''
      simpa [CU, DV] using
        (helperForTheorem_35_6_scaledStep_finiteValues
          (C := C) (D := D) (K := K)
          hC_open hD_open hC_conv hD_conv hFinite hu hv
          (t := t) ht_pos ht_le hu'' hv'')
  have hAxisScaledFinite :
      ∀ {t : ℝ}, 0 < t → t ≤ 1 →
        ∀ {u'' : Fin m → ℝ} {v'' : Fin n → ℝ}, u'' ∈ CU → v'' ∈ DV →
          (K (u + t • u'') v ≠ (⊤ : EReal) ∧ K (u + t • u'') v ≠ (⊥ : EReal)) ∧
            (K u (v + t • v'') ≠ (⊤ : EReal) ∧ K u (v + t • v'') ≠ (⊥ : EReal)) :=
    by
      intro t ht_pos ht_le u'' v'' hu'' hv''
      simpa [CU, DV] using
        (helperForTheorem_35_6_scaledAxisStep_finiteValues
          (C := C) (D := D) (K := K)
          hC_open hD_open hC_conv hD_conv hFinite hu hv
          (t := t) ht_pos ht_le hu'' hv'')
  have hFiniteuv : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFinite u hu v hv
  -- The axis cases are finished already; only the genuinely mixed direction still needs the
  -- direct mixed-quotient convergence argument.
  by_cases hv'0 : v' = 0
  · -- The second-axis case was already settled by the slice derivative theorem.
    simpa [hv'0] using hAxisFirst u'
  by_cases hu'0 : u' = 0
  · -- The first-axis case is symmetric.
    simpa [hu'0] using hAxisSecond v'
  -- Route correction: the direct real squeeze is now available on admissible translated directions,
  -- but the main theorem still needs a clean local scaling/reparameterization step that reduces an
  -- arbitrary non-axis direction `(u', v')` to an admissible pair in `CU × DV` before lifting the
  -- real limit back to the original `EReal` quotient.
  rcases
      helperForTheorem_35_6_exists_posScale_mem_translatedDomains
        (C := C) (D := D) hC_open hD_open hu hv u' v' with
    ⟨ρ, hρpos, huρ, hvρ⟩
  have hScaledReal :
      Filter.Tendsto
        (fun t : ℝ =>
          (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') t).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (Kdir (ρ • u') (ρ • v'))) :=
    helperForTheorem_35_6_mixedQuotient_toReal_tendsto_splitKernelWithin
      (C := C) (D := D) (K := K) (Kdir := Kdir)
      hC_open hD_open hC_conv hD_conv hK hFinite hu hv
      hAxisFirst hAxisSecond hKdir_split huρ hvρ
  have hDivWithin :
      Filter.Tendsto
        (fun t : ℝ => t / ρ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    -- Dividing the step by a fixed positive scalar preserves the right-hand approach to `0`.
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun t : ℝ => t / ρ) ?_ ?_
    · have hDivNhds :
          Filter.Tendsto (fun t : ℝ => t / ρ) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
        have hDivAt : ContinuousAt (fun t : ℝ => t / ρ) (0 : ℝ) :=
          ContinuousAt.div_const continuousAt_id ρ
        simpa [zero_div] using hDivAt.tendsto
      exact hDivNhds.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos ht hρpos
  have hScaledComposed :
      Filter.Tendsto
        (fun t : ℝ =>
          (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') (t / ρ)).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (Kdir (ρ • u') (ρ • v'))) :=
    hScaledReal.comp hDivWithin
  have hRealTransport :
      Filter.Tendsto
        (fun t : ℝ =>
          (1 / ρ) *
            (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') (t / ρ)).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (Kdir u' v')) := by
    have hScaledMul :
        Filter.Tendsto
          (fun t : ℝ =>
            (1 / ρ) *
              (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') (t / ρ)).toReal)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds ((1 / ρ) * Kdir (ρ • u') (ρ • v'))) :=
      Filter.Tendsto.const_mul (1 / ρ) hScaledComposed
    have hScaleCancel : ρ⁻¹ * Kdir (ρ • u') (ρ • v') = Kdir u' v' := by
      rw [hKdir_pos u' v' ρ hρpos]
      field_simp [hρpos.ne']
    simpa [hScaleCancel] using hScaledMul
  have hReparam :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal =
          (1 / ρ) *
            (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') (t / ρ)).toReal :=
    helperForTheorem_35_6_reparametrize_mixedQuotient_by_posScale
      (C := C) (D := D) (K := K)
      hC_open hD_open hC_conv hD_conv hFinite hu hv hρpos huρ hvρ
  have hRealTendsto :
      Filter.Tendsto
        (fun t : ℝ => (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (Kdir u' v')) :=
    Filter.Tendsto.congr'
      ((show
          (fun t : ℝ => (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal) =ᶠ[
            nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
            (fun t : ℝ =>
              (1 / ρ) *
                (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') (t / ρ)).toReal) from
          hReparam).symm)
      hRealTransport
  have hLtRho : Set.Iio ρ ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio ρ, Iio_mem_nhds hρpos, ?_⟩
    intro t ht
    exact ht.1
  have hQuotEq :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        saddleDirectionalDifferenceQuotientAt K u v u' v' t =
          ((((saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal : ℝ) : EReal)) := by
    filter_upwards [self_mem_nhdsWithin, hLtRho] with t ht_pos ht_lt
    have hρne : ρ ≠ 0 := hρpos.ne'
    have ht_div_pos : 0 < t / ρ := div_pos ht_pos hρpos
    have ht_div_le : t / ρ ≤ 1 := by
      rw [div_le_one hρpos]
      exact le_of_lt ht_lt
    have hStepU :
        u + (t / ρ) • (ρ • u') = u + t • u' := by
      have hmul : (t / ρ) * ρ = t := by
        field_simp [hρne]
      calc
        u + (t / ρ) • (ρ • u') = u + (((t / ρ) * ρ) • u') := by rw [smul_smul]
        _ = u + t • u' := by simp [hmul]
    have hStepV :
        v + (t / ρ) • (ρ • v') = v + t • v' := by
      have hmul : (t / ρ) * ρ = t := by
        field_simp [hρne]
      calc
        v + (t / ρ) • (ρ • v') = v + (((t / ρ) * ρ) • v') := by rw [smul_smul]
        _ = v + t • v' := by simp [hmul]
    have hMixedFinite :
        K (u + t • u') (v + t • v') ≠ (⊤ : EReal) ∧
          K (u + t • u') (v + t • v') ≠ (⊥ : EReal) := by
      -- The same shrinking used for reparameterization keeps the mixed evaluation finite.
      simpa [hStepU, hStepV] using
        (hScaledFinite (t := t / ρ) ht_div_pos ht_div_le huρ hvρ)
    have hQuotReal :
        (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal =
          ((K (u + t • u') (v + t • v')).toReal - (K u v).toReal) / t := by
      rw [saddleDirectionalDifferenceQuotientAt, EReal.div_eq_inv_mul, EReal.toReal_mul]
      rw [EReal.toReal_sub hMixedFinite.1 hMixedFinite.2 hFiniteuv.1 hFiniteuv.2]
      have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
        rw [← EReal.coe_inv]
        simp
      rw [hInv]
      ring
    have hQuotEReal :
        saddleDirectionalDifferenceQuotientAt K u v u' v' t =
          ((((K (u + t • u') (v + t • v')).toReal - (K u v).toReal) / t : ℝ) : EReal) := by
      have hNumEq :
          K (u + t • u') (v + t • v') - K u v =
            (((K (u + t • u') (v + t • v')).toReal - (K u v).toReal : ℝ) : EReal) := by
        rw [sub_eq_add_neg]
        simp [sub_eq_add_neg, EReal.coe_toReal hMixedFinite.1 hMixedFinite.2,
          EReal.coe_toReal hFiniteuv.1 hFiniteuv.2]
      rw [saddleDirectionalDifferenceQuotientAt, hNumEq]
      rw [EReal.coe_div]
    calc
      saddleDirectionalDifferenceQuotientAt K u v u' v' t =
          ((((K (u + t • u') (v + t • v')).toReal - (K u v).toReal) / t : ℝ) : EReal) := hQuotEReal
      _ = ((((saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal : ℝ) : EReal)) := by
          congr 1
          exact hQuotReal.symm
  refine ⟨hFiniteuv.1, hFiniteuv.2, ?_⟩
  -- Replace the eventual finite-valued quotient by its real coercion and lift the real limit.
  refine Filter.Tendsto.congr' ?_ ((EReal.tendsto_coe).2 hRealTendsto)
  filter_upwards [hQuotEq] with t ht
  exact ht.symm

/-- Text 35.6.1: the partial subdifferential in the first variable at `(u, v)` consists of the
vectors `u*` such that `K u' v ≤ K u v + ⟪u*, u' - u⟫` for every `u'`. Equivalently, these are
the supergradients of the concave slice `u ↦ K u v` at `u`. -/
def partialSubdifferentialInFirstVariable {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    Set (Fin m → ℝ) :=
  {uStar | ∀ u' : Fin m → ℝ, K u' v ≤ K u v + ((∑ i : Fin m, uStar i * (u' i - u i)) : EReal)}

/-- Text 35.6.2: the partial subdifferential in the second variable at `(u, v)` consists of the
vectors `v*` such that `K u v' ≥ K u v + ⟪v*, v' - v⟫` for every `v'`. Equivalently, these are
the subgradients of the convex slice `v ↦ K u v` at `v`. -/
def partialSubdifferentialInSecondVariable {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {vStar | ∀ v' : Fin n → ℝ, K u v' ≥ K u v + ((∑ i : Fin n, vStar i * (v' i - v i)) : EReal)}

/-- Text 35.6.3: the product subdifferential of `K` at `(u, v)` is
`∂₁ K (u, v) × ∂₂ K (u, v)`. Its elements `(u*, v*)` are the subgradients of `K`
at `(u, v)`. -/
def productSubdifferentialAt {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  partialSubdifferentialInFirstVariable K u v ×ˢ partialSubdifferentialInSecondVariable K u v

/-- A packaged extended-real saddle kernel whose `u`-slices are concave and whose `v`-slices are
convex on the whole space. -/
structure SaddleKernel (m n : ℕ) where
  toFun : (Fin m → ℝ) → (Fin n → ℝ) → EReal
  isSaddle : IsGloballyConcaveConvexERealKernel toFun

/-- Text 35.6.4: for a saddle kernel `K`, the subdifferential is the multivalued mapping
`(u, v) ↦ ∂K(u, v)`. Here `∂K(u, v)` is realized as the product subdifferential from
Text 35.6.3. -/
def saddleSubdifferential {m n : ℕ}
    (K : SaddleKernel m n) :
    ((Fin m → ℝ) × (Fin n → ℝ)) → Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  fun p => productSubdifferentialAt K.toFun p.1 p.2

-- Proof sketch: `∂K(u, v)` is the product of the partial subdifferentials in the first and
-- second variables. For a saddle kernel, these partial subdifferentials are closed convex sets
-- by the one-variable convex/concave subdifferential theory, and the product of closed convex
-- sets is again closed and convex in `ℝ^m × ℝ^n`.
/-- Helper for Text 35.6.5: a finite sum of real products coerced to `EReal` is the coercion of
the corresponding real sum. -/
lemma helperForText_35_6_5_sum_coe_products
    {k : ℕ} (a : Fin k → ℝ) (x : Fin k → ℝ) :
    (∑ i : Fin k, ((x i : ℝ) : EReal) * ((a i : ℝ) : EReal)) =
      (((∑ i : Fin k, x i * a i : ℝ)) : EReal) := by
  -- Induct on the finite sum and use additivity of the real-to-`EReal` coercion.
  classical
  refine Finset.induction_on Finset.univ ?_ ?_
  · simp
  · intro i s hi hs
    simp [hi, hs, EReal.coe_add, EReal.coe_mul]

/-- Helper for Text 35.6.5: every extended-real affine halfspace in a finite-dimensional
Euclidean coordinate space is closed and convex. -/
lemma helperForText_35_6_5_erealAffineHalfspace_isClosed_convex
    {k : ℕ} (α c : EReal) (a : Fin k → ℝ) :
    IsClosed {x : Fin k → ℝ | α ≤ c + ((∑ i : Fin k, x i * a i) : EReal)} ∧
      Convex ℝ {x : Fin k → ℝ | α ≤ c + ((∑ i : Fin k, x i * a i) : EReal)} := by
  -- Split on the constant term in `EReal`, because `⊤`, `⊥`, and finite constants behave
  -- differently under addition.
  revert α
  refine EReal.rec ?_ ?_ ?_ c
  · intro α
    -- When the offset is `⊥`, the halfspace is either `univ` or `∅`.
    revert α
    refine EReal.rec ?_ ?_ ?_
    · have hEq :
          {x : Fin k → ℝ | ((⊥ : EReal) ≤ (⊥ : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (Set.univ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ]
        constructor
        · intro _
          trivial
        · intro _
          exact bot_le
      rw [hEq]
      constructor
      · exact isClosed_univ
      · exact convex_univ
    · intro r
      have hEq :
          {x : Fin k → ℝ | ((r : EReal) ≤ (⊥ : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (∅ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        simp
      rw [hEq]
      constructor
      · exact isClosed_empty
      · exact convex_empty
    · have hEq :
          {x : Fin k → ℝ | ((⊤ : EReal) ≤ (⊥ : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (∅ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        simp
      rw [hEq]
      constructor
      · exact isClosed_empty
      · exact convex_empty
  · intro s α
    -- For a finite offset, only the finite `α` branch yields a genuine real halfspace.
    revert α
    refine EReal.rec ?_ ?_ ?_
    · have hEq :
          {x : Fin k → ℝ | ((⊥ : EReal) ≤ (s : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (Set.univ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ]
        constructor
        · intro _
          trivial
        · intro _
          exact bot_le
      rw [hEq]
      constructor
      · exact isClosed_univ
      · exact convex_univ
    · intro r
      -- Rewrite the `EReal` inequality to an ordinary real affine halfspace.
      have hRewrite :
          {x : Fin k → ℝ | ((r : EReal) ≤ (s : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            {x : Fin k → ℝ | r ≤ s + ∑ i : Fin k, x i * a i} := by
        ext x
        simp only [Set.mem_setOf_eq]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        have hAdd :
            ((s : ℝ) : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) =
              (((s + ∑ i : Fin k, x i * a i : ℝ)) : EReal) := by
          simp [EReal.coe_add]
        rw [hAdd]
        exact EReal.coe_le_coe_iff
      rw [hRewrite]
      constructor
      · -- Closedness comes from continuity of the affine functional.
        have hCont : Continuous fun x : Fin k → ℝ => s + ∑ i : Fin k, x i * a i := by
          fun_prop
        simpa [Set.preimage, Set.setOf_mem_eq] using (isClosed_Ici.preimage hCont)
      · -- Convexity comes from translating `Ici r` and then taking a linear preimage.
        have hTranslate :
            Convex ℝ (((fun y : ℝ => y + s) : ℝ → ℝ) ⁻¹' Set.Ici r) :=
          (convex_Ici r).translate_preimage_left s
        have hLinear : IsLinearMap ℝ (fun x : Fin k → ℝ => ∑ i : Fin k, x i * a i) := by
          refine ⟨?_, ?_⟩
          · intro x y
            simp [Finset.sum_add_distrib, add_mul]
          · intro t x
            simp [Finset.mul_sum, mul_assoc]
        simpa [Set.preimage, Set.setOf_mem_eq, add_comm] using
          Convex.is_linear_preimage (s := (((fun y : ℝ => y + s) : ℝ → ℝ) ⁻¹' Set.Ici r))
            hTranslate hLinear
    · have hEq :
          {x : Fin k → ℝ | ((⊤ : EReal) ≤ (s : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (∅ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        have hAdd :
            ((s : ℝ) : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) =
              (((s + ∑ i : Fin k, x i * a i : ℝ)) : EReal) := by
          simp [EReal.coe_add]
        constructor
        · intro hle
          have hTop :
              (((s + ∑ i : Fin k, x i * a i : ℝ)) : EReal) = (⊤ : EReal) := by
            rw [← hAdd]
            exact top_le_iff.mp hle
          exact EReal.coe_ne_top _ hTop
        · intro hFalse
          exact False.elim hFalse
      rw [hEq]
      constructor
      · exact isClosed_empty
      · exact convex_empty
  · intro α
    -- When the offset is `⊤`, the right-hand side is always `⊤`.
    have hEq :
        {x : Fin k → ℝ | α ≤ (⊤ : EReal) + ((∑ i : Fin k, x i * a i) : EReal)} =
          (Set.univ : Set (Fin k → ℝ)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ]
      rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
      have hTop :
          (⊤ : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) = (⊤ : EReal) := by
        simp
      rw [hTop]
      constructor
      · intro _
        trivial
      · intro _
        exact le_top
    rw [hEq]
    constructor
    · exact isClosed_univ
    · exact convex_univ

/-- Helper for Text 35.6.5: every extended-real affine superhalfspace in a finite-dimensional
Euclidean coordinate space is closed and convex. -/
lemma helperForText_35_6_5_erealAffineSuperhalfspace_isClosed_convex
    {k : ℕ} (α c : EReal) (a : Fin k → ℝ) :
    IsClosed {x : Fin k → ℝ | α ≥ c + ((∑ i : Fin k, x i * a i) : EReal)} ∧
      Convex ℝ {x : Fin k → ℝ | α ≥ c + ((∑ i : Fin k, x i * a i) : EReal)} := by
  -- Split on the constant term in `EReal`, just as in the lower-halfspace case.
  revert α
  refine EReal.rec ?_ ?_ ?_ c
  · intro α
    have hEq :
        {x : Fin k → ℝ | α ≥ (⊥ : EReal) + ((∑ i : Fin k, x i * a i) : EReal)} =
          (Set.univ : Set (Fin k → ℝ)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ]
      constructor
      · intro _
        trivial
      · intro _
        exact bot_le
    rw [hEq]
    constructor
    · exact isClosed_univ
    · exact convex_univ
  · intro s α
    -- For a finite offset, only the finite `α` branch yields a genuine real upper halfspace.
    revert α
    refine EReal.rec ?_ ?_ ?_
    · have hEq :
          {x : Fin k → ℝ | ((⊥ : EReal) ≥ (s : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (∅ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        have hAdd :
            ((s : ℝ) : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) =
              (((s + ∑ i : Fin k, x i * a i : ℝ)) : EReal) := by
          simp [EReal.coe_add]
        constructor
        · intro hle
          have hle' := hle
          rw [hAdd] at hle'
          exact not_le_of_gt (EReal.bot_lt_coe (s + ∑ i : Fin k, x i * a i)) hle'
        · intro hFalse
          exact False.elim hFalse
      rw [hEq]
      constructor
      · exact isClosed_empty
      · exact convex_empty
    · intro r
      -- Rewrite the `EReal` inequality to an ordinary real affine upper halfspace.
      have hRewrite :
          {x : Fin k → ℝ | ((r : EReal) ≥ (s : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            {x : Fin k → ℝ | s + ∑ i : Fin k, x i * a i ≤ r} := by
        ext x
        simp only [Set.mem_setOf_eq]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        have hAdd :
            ((s : ℝ) : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) =
              (((s + ∑ i : Fin k, x i * a i : ℝ)) : EReal) := by
          simp [EReal.coe_add]
        rw [hAdd]
        exact EReal.coe_le_coe_iff
      rw [hRewrite]
      constructor
      · -- Closedness comes from continuity of the affine functional.
        have hCont : Continuous fun x : Fin k → ℝ => s + ∑ i : Fin k, x i * a i := by
          fun_prop
        simpa [Set.preimage, Set.setOf_mem_eq] using (isClosed_Iic.preimage hCont)
      · -- Convexity comes from translating `Iic r` and then taking a linear preimage.
        have hTranslate :
            Convex ℝ (((fun y : ℝ => y + s) : ℝ → ℝ) ⁻¹' Set.Iic r) :=
          (convex_Iic r).translate_preimage_left s
        have hLinear : IsLinearMap ℝ (fun x : Fin k → ℝ => ∑ i : Fin k, x i * a i) := by
          refine ⟨?_, ?_⟩
          · intro x y
            simp [Finset.sum_add_distrib, add_mul]
          · intro t x
            simp [Finset.mul_sum, mul_assoc]
        simpa [Set.preimage, Set.setOf_mem_eq, add_comm] using
          Convex.is_linear_preimage (s := (((fun y : ℝ => y + s) : ℝ → ℝ) ⁻¹' Set.Iic r))
            hTranslate hLinear
    · have hEq :
          {x : Fin k → ℝ | ((⊤ : EReal) ≥ (s : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (Set.univ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ]
        constructor
        · intro _
          trivial
        · intro _
          exact le_top
      rw [hEq]
      constructor
      · exact isClosed_univ
      · exact convex_univ
  · intro α
    -- When the offset is `⊤`, the superhalfspace is either `univ` or `∅`.
    revert α
    refine EReal.rec ?_ ?_ ?_
    · have hEq :
          {x : Fin k → ℝ | ((⊥ : EReal) ≥ (⊤ : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (∅ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        have hTop :
            (⊤ : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) = (⊤ : EReal) := by
          simp
        rw [hTop]
        constructor
        · intro hle
          exact not_le_of_gt (show (⊥ : EReal) < ⊤ by simp) hle
        · intro hFalse
          exact False.elim hFalse
      rw [hEq]
      constructor
      · exact isClosed_empty
      · exact convex_empty
    · intro r
      have hEq :
          {x : Fin k → ℝ | ((r : EReal) ≥ (⊤ : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (∅ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        have hTop :
            (⊤ : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) = (⊤ : EReal) := by
          simp
        rw [hTop]
        constructor
        · intro hle
          exact not_le_of_gt (EReal.coe_lt_top r) hle
        · intro hFalse
          exact False.elim hFalse
      rw [hEq]
      constructor
      · exact isClosed_empty
      · exact convex_empty
    · have hEq :
          {x : Fin k → ℝ | ((⊤ : EReal) ≥ (⊤ : EReal) + ((∑ i : Fin k, x i * a i) : EReal))} =
            (Set.univ : Set (Fin k → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ]
        rw [helperForText_35_6_5_sum_coe_products (a := a) (x := x)]
        have hTop :
            (⊤ : EReal) + (((∑ i : Fin k, x i * a i : ℝ)) : EReal) = (⊤ : EReal) := by
          simp
        rw [hTop]
        constructor
        · intro _
          trivial
        · intro _
          exact le_rfl
      rw [hEq]
      constructor
      · exact isClosed_univ
      · exact convex_univ

/-- Helper for Text 35.6.5: the partial subdifferential in the first variable is an intersection
of closed convex affine halfspaces, hence is itself closed and convex. -/
lemma helperForText_35_6_5_firstPartial_isClosed_convex
    {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    IsClosed (partialSubdifferentialInFirstVariable K u v) ∧
      Convex ℝ (partialSubdifferentialInFirstVariable K u v) := by
  have hEq : partialSubdifferentialInFirstVariable K u v =
      ⋂ u' : Fin m → ℝ,
        {uStar : Fin m → ℝ |
          K u' v ≤ K u v + ((∑ i : Fin m, uStar i * (u' i - u i)) : EReal)} := by
    -- Unfold the definition so the universal quantifier becomes an indexed intersection.
    ext uStar
    simp [partialSubdifferentialInFirstVariable]
  rw [hEq]
  constructor
  · -- Each slice is a closed affine halfspace, and intersections preserve closedness.
    exact isClosed_iInter fun u' : Fin m → ℝ =>
      (helperForText_35_6_5_erealAffineHalfspace_isClosed_convex
        (α := K u' v) (c := K u v) (a := fun i => u' i - u i)).1
  · -- The same intersection description preserves convexity.
    exact convex_iInter fun u' : Fin m → ℝ =>
      (helperForText_35_6_5_erealAffineHalfspace_isClosed_convex
        (α := K u' v) (c := K u v) (a := fun i => u' i - u i)).2

/-- Helper for Text 35.6.5: the partial subdifferential in the second variable is an intersection
of closed convex affine halfspaces, hence is itself closed and convex. -/
lemma helperForText_35_6_5_secondPartial_isClosed_convex
    {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    IsClosed (partialSubdifferentialInSecondVariable K u v) ∧
      Convex ℝ (partialSubdifferentialInSecondVariable K u v) := by
  have hEq : partialSubdifferentialInSecondVariable K u v =
      ⋂ v' : Fin n → ℝ,
        {vStar : Fin n → ℝ |
          K u v' ≥ K u v + ((∑ i : Fin n, vStar i * (v' i - v i)) : EReal)} := by
    -- Unfold the definition so the universal quantifier becomes an indexed intersection.
    ext vStar
    simp [partialSubdifferentialInSecondVariable]
  rw [hEq]
  constructor
  · -- Each slice is a closed affine halfspace, and intersections preserve closedness.
    exact isClosed_iInter fun v' : Fin n → ℝ =>
      (helperForText_35_6_5_erealAffineSuperhalfspace_isClosed_convex
        (α := K u v') (c := K u v) (a := fun i => v' i - v i)).1
  · -- The same intersection description preserves convexity.
    exact convex_iInter fun v' : Fin n → ℝ =>
      (helperForText_35_6_5_erealAffineSuperhalfspace_isClosed_convex
        (α := K u v') (c := K u v) (a := fun i => v' i - v i)).2

/-- Text 35.6.5: for every `(u, v) ∈ ℝ^m × ℝ^n`, the set `∂K(u, v)` is a possibly empty closed
convex subset of `ℝ^m × ℝ^n`. -/
theorem section35_text35_6_5
    {m n : ℕ}
    (K : SaddleKernel m n)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    IsClosed (saddleSubdifferential K (u, v)) ∧
      Convex ℝ (saddleSubdifferential K (u, v)) := by
  -- Route correction: the direct definitional proof avoids the finiteness hypotheses hidden in
  -- one-variable subdifferential closure theorems by rewriting `∂K(u, v)` as a product of
  -- intersections of affine halfspaces.
  have hFirst := helperForText_35_6_5_firstPartial_isClosed_convex K.toFun u v
  have hSecond := helperForText_35_6_5_secondPartial_isClosed_convex K.toFun u v
  constructor
  · -- Closedness is preserved under products once both partial subdifferentials are closed.
    simpa [saddleSubdifferential, productSubdifferentialAt] using hFirst.1.prod hSecond.1
  · -- Convexity is preserved under products once both partial subdifferentials are convex.
    simpa [saddleSubdifferential, productSubdifferentialAt] using hFirst.2.prod hSecond.2

end Section35
end Chap07
