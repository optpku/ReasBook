/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part7

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- The first-variable directional derivative function attached to a saddle kernel at `(u, v)`,
defined by `u' ↦ -K'(u, v; -u', 0)` using the infimum of all admissible directional-derivative
values. -/
noncomputable def firstVariableDirectionalDerivativeFunction {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    (Fin m → ℝ) → EReal :=
  fun u' => -sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v (-u') 0 L}

/-- The lower semicontinuous hull of an extended-real-valued function, realized by the closure of
its epigraph. -/
noncomputable def saddleLowerSemicontinuousHull {α : Type*} [TopologicalSpace α]
    (f : α → EReal) : α → EReal :=
  fun x => sInf {r : EReal | (x, r) ∈ closure {p : α × EReal | f p.1 ≤ p.2}}

/-- The support function of a set of vectors in `ℝ^m`, viewed as an extended-real-valued function
on `ℝ^m`. -/
noncomputable def supportFunctionOfSet {m : ℕ} (S : Set (Fin m → ℝ)) :
    (Fin m → ℝ) → EReal :=
  fun u' =>
    sSup ((fun uStar : Fin m → ℝ => (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) '' S)

/-- Helper for Text 35.6.6: the reflected first slice `x ↦ -K (-x) v` is convex, because the
saddle hypothesis already gives convexity of `x ↦ -K x v` and the involution `x ↦ -x` is linear.
-/
lemma helperForText_35_6_6_reflectedFirstSlice_convex
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    (v : Fin n → ℝ) :
    ConvexFunction (fun x : Fin m → ℝ => -K (-x) v) := by
  -- Start from the convexity of the unrecentered first slice supplied by the saddle hypothesis.
  have hslice : ConvexFunction (fun x : Fin m → ℝ => -K x v) := by
    simpa using hSaddle.1 v
  have hconvOn :
      ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun x : Fin m → ℝ => -K (-x) v) := by
    -- Precomposing by the linear involution `x ↦ -x` preserves convexity on the whole space.
    simpa using
      (convexFunctionOn_precomp_linearMap
        (A := (-LinearMap.id : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)))
        (g := fun x : Fin m → ℝ => -K x v) (by simpa [ConvexFunction] using hslice))
  -- The ambient domain is `Set.univ`, so convexity-on-univ is ordinary convexity.
  simpa [ConvexFunction] using hconvOn

/-- Helper for Text 35.6.6: recentering the first slice at `-u` does not change the finiteness of
the base value, because the reflected slice still evaluates to `-K u v`. -/
lemma helperForText_35_6_6_reflectedFirstSlice_finiteAtBase
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    (fun x : Fin m → ℝ => -K (-x) v) (-u) ≠ (⊤ : EReal) ∧
      (fun x : Fin m → ℝ => -K (-x) v) (-u) ≠ (⊥ : EReal) := by
  -- Negation swaps `⊤` and `⊥`, so the reflected slice is finite exactly when `K u v` is finite.
  exact ⟨by simpa using hFinite.2, by simpa using hFinite.1⟩

/-- Helper for Text 35.6.6: after recentering the first slice by `x ↦ -x`, the textbook
first-variable directional derivative function is exactly the ordinary upper directional derivative
of the convex slice `x ↦ -K (-x) v` at the base point `-u`. -/
lemma helperForText_35_6_6_recenteredFirstSlice_directionalDerivative
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (u' : Fin m → ℝ) :
    firstVariableDirectionalDerivativeFunction K u v u' =
      upperDirectionalDerivativeAt (fun x => -K (-x) v) (-u) u' := by
  let g : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  have hg : ConvexFunction g := by
    -- Reuse the reflected-slice convexity lemma so the recentering argument stays isolated.
    simpa [g] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hSaddle v
  have hgu : g (-u) ≠ (⊤ : EReal) ∧ g (-u) ≠ (⊥ : EReal) := by
    -- Reuse the reflected-base finiteness lemma so the limit argument only handles derivatives.
    simpa [g] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase (K := K) (u := u) (v := v) hFinite
  let S : Set EReal := {L : EReal | IsSaddleDirectionalDerivativeAt K u v (-u') 0 L}
  have hright :
      Filter.Tendsto
        (directionalDifferenceQuotientAt g (-u) u')
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt g (-u) u')) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear g hg (-u) hgu).1 u' |>.2.1
  have hneg :
      Filter.Tendsto
        (fun t : ℝ => -directionalDifferenceQuotientAt g (-u) u' t)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (-upperDirectionalDerivativeAt g (-u) u')) := by
    -- Negating the convex-slice quotient recovers the sign convention of `φ(u') = -K'(u,v;-u',0)`.
    simpa using hright.neg
  have hEventuallyEq :
      (fun t : ℝ => saddleDirectionalDifferenceQuotientAt K u v (-u') 0 t) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
        (fun t : ℝ => -directionalDifferenceQuotientAt g (-u) u' t) := by
    -- Unfolding the two quotients shows that the saddle quotient is literally the negated slice
    -- quotient after the recentering `x ↦ -x`.
    filter_upwards with t
    symm
    rw [directionalDifferenceQuotientAt, saddleDirectionalDifferenceQuotientAt,
      EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
    rw [EReal.neg_sub (Or.inr hgu.2) (Or.inr hgu.1)]
    rw [← EReal.div_eq_inv_mul]
    simp [g, sub_eq_add_neg, add_comm]
  have hmem : -upperDirectionalDerivativeAt g (-u) u' ∈ S := by
    -- The recentered slice derivative produces a concrete witness in the defining infimum set.
    refine ⟨hFinite.1, hFinite.2, ?_⟩
    simpa [S] using Filter.Tendsto.congr' hEventuallyEq.symm hneg
  have hunique : ∀ L ∈ S, L = -upperDirectionalDerivativeAt g (-u) u' := by
    intro L hL
    rcases hL with ⟨_, _, hLlim⟩
    -- Both candidates are limits of the same quotient family, so uniqueness of limits identifies them.
    exact tendsto_nhds_unique hLlim (Filter.Tendsto.congr' hEventuallyEq.symm hneg)
  have hS_nonempty : S.Nonempty := ⟨-upperDirectionalDerivativeAt g (-u) u', hmem⟩
  have hsInf_eq : sInf S = -upperDirectionalDerivativeAt g (-u) u' := by
    -- Since the defining set is a singleton up to equality, its infimum is that unique value.
    refine le_antisymm ?_ ?_
    · exact sInf_le hmem
    · exact le_csInf hS_nonempty (by intro L hL; rw [hunique L hL])
  calc
    firstVariableDirectionalDerivativeFunction K u v u' = -sInf S := by
      rfl
    _ = -(-upperDirectionalDerivativeAt g (-u) u') := by
      rw [hsInf_eq]
    _ = upperDirectionalDerivativeAt g (-u) u' := by
      simp

/-- Helper for Text 35.6.6: the whole textbook first-variable directional-derivative function is
exactly the Chapter 23 directional derivative of the reflected first slice at `-u`. -/
lemma helperForText_35_6_6_firstVariableDirectionalDerivative_eq_upperDirectionalDerivative
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    firstVariableDirectionalDerivativeFunction K u v =
      upperDirectionalDerivativeAt (fun x => -K (-x) v) (-u) := by
  -- Upgrade the pointwise recentering identity to an equality of functions.
  funext u'
  exact
    helperForText_35_6_6_recenteredFirstSlice_directionalDerivative
      (K := K) hSaddle (u := u) (v := v) hFinite u'

/-- Helper for Text 35.6.6: membership in the Euclidean subdifferential of the reflected slice is
exactly the textbook first-partial supporting inequality. -/
lemma helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {uStar : Fin m → ℝ} :
    dotProductEquiv ℝ (Fin m) uStar ∈ subdifferentialAt (fun x => -K (-x) v) (-u) ↔
      uStar ∈ partialSubdifferentialInFirstVariable K u v := by
  have hsumTransport : ∀ w : Fin m → ℝ,
      (((∑ i : Fin m, uStar i * (w i - u i) : ℝ)) : EReal) =
        ∑ i : Fin m, (((uStar i : ℝ) : EReal) * ((((w i - u i : ℝ)) : EReal))) := by
    intro w
    classical
    -- Expand the real sum term-by-term so it matches the `EReal` sum used in the file.
    refine Finset.induction_on Finset.univ ?_ ?_
    · simp
    · intro i s hi hs
      simp [hi, hs, EReal.coe_add, EReal.coe_mul]
  have hreflectedDot : ∀ w : Fin m → ℝ,
      ((dotProductEquiv ℝ (Fin m) uStar) ((-w) - -u) : ℝ) =
        -(∑ i : Fin m, uStar i * (w i - u i) : ℝ) := by
    intro w
    -- The reflected increment contributes the negative of the ordinary first-variable pairing.
    simp [dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, add_comm]
  constructor
  · intro hu
    rw [mem_subdifferentialAt_iff] at hu
    intro u'
    -- Evaluate the reflected-slice subgradient inequality at the reflected test point `-u'`.
    have hineq := hu (-u')
    have hraw :
        -K u' v ≥ -K u v +
          (((dotProductEquiv ℝ (Fin m) uStar) ((-u') - -u) : ℝ) : EReal) := by
      simpa [dotProductEquiv_apply_apply] using hineq
    let a : EReal := (((dotProductEquiv ℝ (Fin m) uStar) ((-u') - -u) : ℝ) : EReal)
    -- Move the inequality back across negation so that it points in the textbook direction.
    have hneg :
        K u' v ≤ -(a + -K u v) := by
      simpa [a, add_comm, add_left_comm, add_assoc] using (EReal.le_neg.2 hraw)
    have hsum :
        -(a + -K u v) =
          K u v + (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := by
      have hbot : a ≠ (⊥ : EReal) := by
        simp [a]
      have htop : a ≠ (⊤ : EReal) := by
        exact EReal.coe_ne_top _
      -- The reflected pairing equals the negative of the ordinary first-variable pairing.
      calc
        -(a + -K u v) = -a - (-K u v) := by
          simpa using EReal.neg_add (Or.inl hbot) (Or.inl htop)
        _ = -a + K u v := by
          simp [sub_eq_add_neg]
        _ = K u v + (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := by
          have ha :
              a = (((-(∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : ℝ) : EReal) := by
            simpa [a] using
              congrArg (fun r : ℝ => (r : EReal)) (hreflectedDot (w := u'))
          rw [add_comm]
          rw [ha]
          simp
    have hneg' :
        K u' v ≤ K u v + (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := by
      simpa [hsum] using hneg
    simpa [partialSubdifferentialInFirstVariable, hsumTransport (w := u')] using hneg'
  · intro hu
    rw [mem_subdifferentialAt_iff]
    intro z
    -- Apply the textbook inequality to the reflected point `-z`.
    have hineq0 := hu (-z)
    have hsumNeg :
        (((∑ i : Fin m, uStar i * (((-z) i) - u i) : ℝ)) : EReal) =
          ∑ i : Fin m, (((uStar i : ℝ) : EReal) * ((↑((-z) i) : EReal) - ↑(u i))) := by
      calc
        (((∑ i : Fin m, uStar i * (((-z) i) - u i) : ℝ)) : EReal) =
            ∑ i : Fin m, (((uStar i : ℝ) : EReal) * (((( (-z) i - u i : ℝ)) : EReal))) := by
              simpa using hsumTransport (w := -z)
        _ = ∑ i : Fin m, (((uStar i : ℝ) : EReal) * ((↑((-z) i) : EReal) - ↑(u i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp
    have hineq :
        K (-z) v ≤ K u v + (((∑ i : Fin m, uStar i * (((-z) i) - u i) : ℝ)) : EReal) := by
      have hshape :
          K u v +
              ∑ i : Fin m, (((uStar i : ℝ) : EReal) * ((↑((-z) i) : EReal) - ↑(u i))) =
            K u v + (((∑ i : Fin m, uStar i * (((-z) i) - u i) : ℝ)) : EReal) := by
        rw [hsumNeg]
      exact hshape ▸ hineq0
    let a : EReal := (((dotProductEquiv ℝ (Fin m) uStar) (z - -u) : ℝ) : EReal)
    have hrewrite :
        K (-z) v ≤ -(a + -K u v) := by
      calc
        K (-z) v ≤ K u v + (((∑ i : Fin m, uStar i * (((-z) i) - u i) : ℝ)) : EReal) := hineq
        _ = -(a + -K u v) := by
          have hbot : a ≠ (⊥ : EReal) := by
            simp [a]
          have htop : a ≠ (⊤ : EReal) := by
            exact EReal.coe_ne_top _
          -- The reflected increment again becomes the negative of the ordinary pairing.
          calc
            K u v + (((∑ i : Fin m, uStar i * (((-z) i) - u i) : ℝ)) : EReal) = -a + K u v := by
              have ha :
                  a = (((-(∑ i : Fin m, uStar i * (((-z) i) - u i) : ℝ)) : ℝ) : EReal) := by
                simpa [a] using
                  congrArg (fun r : ℝ => (r : EReal)) (hreflectedDot (w := -z))
              rw [add_comm]
              rw [ha]
              simp
            _ = -a - (-K u v) := by
              simp [sub_eq_add_neg]
            _ = -(a + -K u v) := by
              simpa using (EReal.neg_add (Or.inl hbot) (Or.inl htop)).symm
    -- Pull the inequality across `EReal.le_neg` to recover the reflected subgradient form.
    have hfinal : a + -K u v ≤ -K (-z) v := (EReal.le_neg).1 hrewrite
    simpa [a, dotProductEquiv_apply_apply, add_comm, add_left_comm, add_assoc] using hfinal

/-- Helper for Text 35.6.6: the Euclidean subdifferential of the recentered convex slice
`x ↦ -K (-x) v` at `-u` is exactly the first partial subdifferential `∂₁ K(u, v)`. -/
lemma helperForText_35_6_6_partialFirst_eq_sliceSubdifferential
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt (fun x => -K (-x) v) (-u)) =
      partialSubdifferentialInFirstVariable K u v := by
  ext uStar
  -- After the pointwise sign normalization, the set equality is just extensionality.
  exact helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
    (K := K) (u := u) (v := v) (uStar := uStar)

/-- Helper for Text 35.6.6: after identifying the slice subdifferential with `∂₁ K(u, v)`, the
Chapter 23 support value is exactly the textbook support function of the first partial
subdifferential. -/
lemma helperForText_35_6_6_supportFunctionOfSet_eq_supportFunctionEReal
    {m : ℕ} (S : Set (Fin m → ℝ)) :
    supportFunctionEReal S = supportFunctionOfSet S := by
  funext u'
  -- Unfold both support functions and identify their defining image sets pointwise.
  unfold supportFunctionEReal supportFunctionOfSet
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp [dotProduct]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp [dotProduct]⟩

/-- Helper for Text 35.6.6: after identifying the slice subdifferential with `∂₁ K(u, v)`, the
Chapter 23 support value is exactly the textbook support function of the first partial
subdifferential. -/
lemma helperForText_35_6_6_sliceSupport_eq_firstPartialSupport
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    subdifferentialSupportAt (fun x => -K (-x) v) (-u) =
      supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) := by
  funext u'
  -- Rewrite the dual-valued support via the Euclidean representative set.
  calc
    subdifferentialSupportAt (fun x => -K (-x) v) (-u) u' =
        supportFunctionEReal
          (((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt (fun x => -K (-x) v) (-u)) ) u' := by
      symm
      exact
        helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq
          (fun x => -K (-x) v) (-u) u'
    _ = supportFunctionEReal (partialSubdifferentialInFirstVariable K u v) u' := by
      rw [helperForText_35_6_6_partialFirst_eq_sliceSubdifferential (K := K) (u := u) (v := v)]
    _ = supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) u' := by
      rw [← helperForText_35_6_6_supportFunctionOfSet_eq_supportFunctionEReal]

/-- Helper for Text 35.6.6: restricting a closure computation to an open neighborhood of the base
point does not change membership, so localizing to the finite-height `EReal` range is legitimate. -/
lemma helperForText_35_6_6_mem_closure_inter_open_iff
    {α : Type*} [TopologicalSpace α]
    {s t : Set α} {x : α}
    (hx : x ∈ t) (ht : IsOpen t) :
    x ∈ closure s ↔ x ∈ closure (s ∩ t) := by
  constructor
  · intro hs
    -- Intersect the neighborhood with the open range set so the closure test stays local.
    rw [mem_closure_iff] at hs ⊢
    intro U hU hxU
    have hnonempty : (U ∩ t ∩ s).Nonempty := hs (U ∩ t) (hU.inter ht) ⟨hxU, hx⟩
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hnonempty
  · intro hs
    -- The localized set is smaller, so its closure still lies in the original closure.
    exact closure_mono (Set.inter_subset_left) hs

/-- Helper for Text 35.6.6: a finite `EReal` height lies in the closure of the full `EReal`
epigraph exactly when the corresponding real height lies in the closure of the ordinary real
epigraph. -/
lemma helperForText_35_6_6_realHeight_mem_saddleClosure_iff_realEpigraphClosure
    {m : ℕ} (φ : (Fin m → ℝ) → EReal) (x : Fin m → ℝ) (r : ℝ) :
    ((x, (r : EReal)) ∈ closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2}) ↔
      ((x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ)) := by
  let ι : ((Fin m → ℝ) × ℝ) → ((Fin m → ℝ) × EReal) := fun p => (p.1, (p.2 : EReal))
  have hEmb : Topology.IsEmbedding ι := by
    -- The real-height embedding is the identity on the horizontal coordinate and `ℝ ↪ EReal`
    -- on the vertical coordinate.
    simpa [ι] using (Topology.IsEmbedding.id.prodMap EReal.isEmbedding_coe)
  have hOpenEmb : Topology.IsOpenEmbedding ι := by
    -- The same product map is an open embedding because the `EReal` coercion is open.
    simpa [ι] using
      ((Topology.IsOpenEmbedding.id : Topology.IsOpenEmbedding (fun q : Fin m → ℝ => q)).prodMap
        EReal.isOpenEmbedding_coe)
  have hOpenRange : IsOpen (Set.range ι) := by
    -- Finite-height points form an open range in the ambient `EReal` epigraph space.
    simpa using hOpenEmb.isOpen_range
  have hRange : (x, (r : EReal)) ∈ Set.range ι := ⟨(x, r), rfl⟩
  have himage :
      ι '' epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ =
        {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} ∩ Set.range ι := by
    -- Inside the finite-height range, the full `EReal` epigraph is exactly the image
    -- of the real epigraph.
    ext p
    rcases p with ⟨y, μ⟩
    constructor
    · rintro ⟨⟨z, s⟩, hp, hEq⟩
      have hEq' : (z, (s : EReal)) = (y, μ) := by
        simpa [ι] using hEq
      rcases Prod.mk.inj hEq' with ⟨hzy, hμs⟩
      refine ⟨?_, ?_⟩
      · simpa [hzy, hμs] using (mem_epigraph_univ_iff (f := φ)).1 hp
      · exact ⟨(z, s), by simpa [ι] using hEq⟩
    · rintro ⟨hp, ⟨⟨z, s⟩, hEq⟩⟩
      have hEq' : (z, (s : EReal)) = (y, μ) := by
        simpa [ι] using hEq
      rcases Prod.mk.inj hEq' with ⟨hzy, hμs⟩
      refine ⟨(z, s), ?_, hEq⟩
      · exact (mem_epigraph_univ_iff (f := φ)).2 (by simpa [hzy, hμs] using hp)
  have hRangeRestriction :
      (x, (r : EReal)) ∈ closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} ↔
        (x, (r : EReal)) ∈
          closure ({p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} ∩ Set.range ι) :=
    helperForText_35_6_6_mem_closure_inter_open_iff
      (α := (Fin m → ℝ) × EReal)
      (s := {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2})
      (t := Set.range ι) (x := (x, (r : EReal))) hRange hOpenRange
  have hEmbedClosure :
      ι (x, r) ∈ closure (ι '' epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) ↔
        (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) := by
    have hclosure :
        closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) =
          ι ⁻¹' closure (ι '' epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) := by
      -- Open embeddings transport closure by preimage.
      simpa [ι] using
        hEmb.closure_eq_preimage_closure_image
          (s := epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ)
    simpa [hclosure]
  have hEmbedClosure' :
      (x, (r : EReal)) ∈ closure (ι '' epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) ↔
        (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) := by
    simpa [ι] using hEmbedClosure
  have hEmbedClosure'' :
      (x, (r : EReal)) ∈
          closure ({p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} ∩ Set.range ι) ↔
        (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) := by
    simpa [himage] using hEmbedClosure'
  -- After restricting to the finite-height range, the two closure conditions are identical.
  exact hRangeRestriction.trans hEmbedClosure''

/-- Helper for Text 35.6.6: the closure of the full `EReal` epigraph remains upward closed in the
second coordinate. -/
lemma helperForText_35_6_6_saddleClosure_upwardInSecondCoordinate
    {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    {x : Fin m → ℝ} {μ ν : EReal}
    (hμν : μ ≤ ν)
    (hx : (x, μ) ∈ closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2}) :
    (x, ν) ∈ closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} := by
  let T : ((Fin m → ℝ) × EReal) → ((Fin m → ℝ) × EReal) := fun p => (p.1, max p.2 ν)
  have hcont : Continuous T := by
    -- The map that raises the second coordinate to at least `ν` is continuous.
    have hsnd : Continuous (fun p : (Fin m → ℝ) × EReal => max p.2 ν) := by
      simpa [max_def] using (continuous_snd.max continuous_const)
    exact continuous_fst.prodMk hsnd
  have himage :
      T '' {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} ⊆
        {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} := by
    -- Raising the height preserves epigraph membership.
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩
    exact le_trans (by simpa using hq) (le_max_left _ _)
  have hximage :
      T (x, μ) ∈ closure (T '' {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2}) := by
    -- Continuity sends closure points to closure points of the image.
    have hsubset :=
      image_closure_subset_closure_image (f := T)
        (s := {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2}) hcont
    exact hsubset ⟨(x, μ), hx, rfl⟩
  have hclosure :
      closure (T '' {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2}) ⊆
        closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} :=
    closure_mono himage
  have hT : T (x, μ) = (x, ν) := by
    simp [T, max_eq_right hμν]
  -- Apply the height-raising map at the specific closure point `(x, μ)`.
  exact hclosure (by simpa [hT] using hximage)

/-- Helper for Text 35.6.6: the `EReal` epigraph hull used for saddle kernels is exactly the
Chapter 2 vertical-slice infimum `epigraphClosureInf`. -/
lemma helperForText_35_6_6_saddleLowerHull_eq_epigraphClosureInf
    {m : ℕ} (φ : (Fin m → ℝ) → EReal) :
    saddleLowerSemicontinuousHull φ = epigraphClosureInf φ := by
  funext x
  let A : Set EReal :=
    {μ : EReal | (x, μ) ∈ closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2}}
  let C : Set EReal :=
    {μ : EReal |
      ∃ r : ℝ, μ = (r : EReal) ∧
        (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ)}
  have hC_to_A : C ⊆ A := by
    intro μ hμ
    rcases hμ with ⟨r, rfl, hr⟩
    -- Every finite-height real-epigraph witness is also a witness in the ambient `EReal` closure.
    simpa [A] using
      (helperForText_35_6_6_realHeight_mem_saddleClosure_iff_realEpigraphClosure
        (φ := φ) (x := x) (r := r)).2 hr
  have hA_nonempty : A.Nonempty := by
    -- The top height always lies in the epigraph, hence also in its closure.
    refine ⟨⊤, ?_⟩
    show (x, (⊤ : EReal)) ∈ closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2}
    apply subset_closure
    simp
  have hsInfA_le_sInfC : sInf A ≤ sInf C := by
    by_cases hC_nonempty : C.Nonempty
    · -- The full-epigraph infimum is below every finite-height witness.
      exact le_csInf hC_nonempty (fun μ hμ => sInf_le (hC_to_A hμ))
    · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
      simp [hC_empty]
  have hsInfC_le_sInfA : sInf C ≤ sInf A := by
    refine le_csInf hA_nonempty ?_
    intro μ hμ
    rcases (EReal.exists (p := fun z : EReal => z = μ)).1 ⟨μ, rfl⟩ with
      hμbot | hμtop | hμreal
    · -- If the ambient closure contains height `⊥`, upward closure forces every real height into
      -- the real epigraph closure, so the slice infimum is also `⊥`.
      have hAllReal : ∀ r : ℝ, ((r : EReal) ∈ C) := by
        intro r
        refine ⟨r, rfl, ?_⟩
        have hfull :
            (x, (r : EReal)) ∈ closure {p : (Fin m → ℝ) × EReal | φ p.1 ≤ p.2} :=
          helperForText_35_6_6_saddleClosure_upwardInSecondCoordinate
            (φ := φ) (x := x) (μ := ⊥) (ν := (r : EReal)) bot_le
            (by simpa [A, eq_comm] using hμbot ▸ hμ)
        exact
          (helperForText_35_6_6_realHeight_mem_saddleClosure_iff_realEpigraphClosure
            (φ := φ) (x := x) (r := r)).1 hfull
      have hbot : sInf C = (⊥ : EReal) := by
        have hle_all : ∀ r : ℝ, sInf C ≤ (r : EReal) := by
          intro r
          exact sInf_le (hAllReal r)
        rcases (EReal.exists (p := fun z : EReal => z = sInf C)).1 ⟨sInf C, rfl⟩ with
          hsBot | hsTop | hsReal
        · simpa [eq_comm] using hsBot
        · exfalso
          have : ¬ ((⊤ : EReal) ≤ (0 : EReal)) := by simp
          exact this (hsTop.symm ▸ hle_all 0)
        · rcases hsReal with ⟨a, ha⟩
          have : ¬ ((a : EReal) ≤ ((a - 1 : ℝ) : EReal)) := by
            apply not_le_of_gt
            exact_mod_cast (show a - 1 < a by linarith)
          exact (this (ha.symm ▸ hle_all (a - 1))).elim
      simpa [hbot, eq_comm] using hμbot
    · simpa [hμtop] using (show sInf C ≤ (⊤ : EReal) from le_top)
    · rcases hμreal with ⟨r, hμr⟩
      have hr : (r : EReal) ∈ C := by
        refine ⟨r, rfl, ?_⟩
        exact
          (helperForText_35_6_6_realHeight_mem_saddleClosure_iff_realEpigraphClosure
            (φ := φ) (x := x) (r := r)).1
            (by simpa [A, hμr] using hμ)
      have hle : sInf C ≤ (r : EReal) := sInf_le hr
      simpa [hμr] using hle
  have hEqSetInf : sInf A = sInf C := le_antisymm hsInfA_le_sInfC hsInfC_le_sInfA
  calc
    saddleLowerSemicontinuousHull φ x = sInf A := by
      rfl
    _ = sInf C := hEqSetInf
    _ = epigraphClosureInf φ x := by
      -- `kCl_eq_epigraphClosureInf` is exactly the Chapter 2 identification of the finite-height
      -- slice infimum with `epigraphClosureInf`.
      simpa [C] using congrFun (kCl_eq_epigraphClosureInf (n := m) (k := φ)) x

/-- Helper for Text 35.6.6: the closure-by-epigraph construction `epigraphClosureInf` is exactly
the ordinary lower semicontinuous hull. -/
lemma helperForText_35_6_6_epigraphClosureInf_eq_lowerSemicontinuousHull
    {m : ℕ} (φ : (Fin m → ℝ) → EReal) :
    epigraphClosureInf φ = lowerSemicontinuousHull φ := by
  let g : (Fin m → ℝ) → EReal := lowerSemicontinuousHull φ
  have hspec :=
    Classical.choose_spec (exists_lowerSemicontinuousHull (n := m) φ)
  have hgLsc : LowerSemicontinuous g := by
    simpa [g] using hspec.1
  have hgLe : g ≤ φ := by
    simpa [g] using hspec.2.1
  have hEpigraphClosure :
      epigraph (S := (Set.univ : Set (Fin m → ℝ))) (epigraphClosureInf φ) =
        closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) := by
    -- The closed epigraph of `epigraphClosureInf` is, by construction, the closure of the
    -- original epigraph.
    simpa using (closure_epigraph_eq_epigraph_sInf (f := φ))
  have hHullLsc : LowerSemicontinuous (epigraphClosureInf φ) := by
    -- Closedness of the epigraph is exactly lower semicontinuity.
    have hclosedEpigraph :
        IsClosed (epigraph (S := (Set.univ : Set (Fin m → ℝ))) (epigraphClosureInf φ)) := by
      simpa [hEpigraphClosure] using isClosed_closure
    have hclosedSublevel :
        ∀ α : ℝ, IsClosed {x | epigraphClosureInf φ x ≤ (α : EReal)} :=
      closed_sublevel_of_closed_epigraph (f := epigraphClosureInf φ) hclosedEpigraph
    exact (lowerSemicontinuous_iff_closed_sublevel (f := epigraphClosureInf φ)).2 hclosedSublevel
  have hHullLe : epigraphClosureInf φ ≤ φ := by
    intro x
    by_cases htop : φ x = (⊤ : EReal)
    · simp [htop]
    by_cases hbot : φ x = (⊥ : EReal)
    · have hHullBot : epigraphClosureInf φ x = (⊥ : EReal) := by
        apply (EReal.eq_bot_iff_forall_lt (x := epigraphClosureInf φ x)).2
        intro μ
        have hleAll : ∀ r : ℝ, epigraphClosureInf φ x ≤ (r : EReal) := by
          intro r
          have hxEpigraph :
              (x, r) ∈ epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ := by
            exact (mem_epigraph_univ_iff (f := φ)).2 (by simp [hbot])
          have hxMem :
              (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) :=
            subset_closure hxEpigraph
          have hmem :
              ((r : ℝ) : EReal) ∈
                (fun t : ℝ => (t : EReal)) '' {t : ℝ |
                  (x, t) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ)} :=
            ⟨r, hxMem, rfl⟩
          exact sInf_le hmem
        have hlt : (((μ - 1 : ℝ)) : EReal) < (μ : EReal) := by
          exact_mod_cast (show μ - 1 < μ by linarith)
        exact lt_of_le_of_lt (hleAll (μ - 1)) hlt
      simp [hbot, hHullBot]
    have hxMem :
        (x, (φ x).toReal) ∈
          closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) := by
      have hleToReal : φ x ≤ (φ x).toReal := EReal.le_coe_toReal htop
      have hxEpigraph :
          (x, (φ x).toReal) ∈ epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ :=
        (mem_epigraph_univ_iff (f := φ)).2 hleToReal
      exact subset_closure hxEpigraph
    have hleToReal :
        epigraphClosureInf φ x ≤ (φ x).toReal := by
      have hmem :
          (((φ x).toReal : ℝ) : EReal) ∈
            (fun t : ℝ => (t : EReal)) '' {t : ℝ |
              (x, t) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ)} :=
        ⟨(φ x).toReal, hxMem, rfl⟩
      exact sInf_le hmem
    have hcoe : (((φ x).toReal : ℝ) : EReal) = φ x := EReal.coe_toReal htop hbot
    simpa [hcoe] using hleToReal
  have hEpigraphClosureLe :
      epigraphClosureInf φ ≤ lowerSemicontinuousHull φ :=
    hspec.2.2 (epigraphClosureInf φ) hHullLsc hHullLe
  have hclosureSubset :
      closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) φ) ⊆
        epigraph (S := (Set.univ : Set (Fin m → ℝ))) g :=
    closure_epigraph_subset_epigraph_of_lsc_le (f := φ) (g := g) hgLsc hgLe
  have hsubset :
      epigraph (S := (Set.univ : Set (Fin m → ℝ))) (epigraphClosureInf φ) ⊆
        epigraph (S := (Set.univ : Set (Fin m → ℝ))) g := by
    simpa [hEpigraphClosure] using hclosureSubset
  have hLowerHullLe :
      lowerSemicontinuousHull φ ≤ epigraphClosureInf φ := by
    intro x
    by_cases htop : epigraphClosureInf φ x = (⊤ : EReal)
    · simp [htop]
    by_cases hbot : epigraphClosureInf φ x = (⊥ : EReal)
    · have hforall : ∀ μ : ℝ, g x ≤ (μ : EReal) := by
        intro μ
        have hxEpigraph :
            (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin m → ℝ))) (epigraphClosureInf φ) := by
          exact (mem_epigraph_univ_iff (f := epigraphClosureInf φ)).2 (by simp [hbot])
        exact (mem_epigraph_univ_iff (f := g)).1 (hsubset hxEpigraph)
      have hbot' : g x = (⊥ : EReal) := by
        apply (EReal.eq_bot_iff_forall_lt (x := g x)).2
        intro μ
        have hlt : (((μ - 1 : ℝ)) : EReal) < (μ : EReal) := by
          exact_mod_cast (show μ - 1 < μ by linarith)
        exact lt_of_le_of_lt (hforall (μ - 1)) hlt
      simp [g, hbot, hbot']
    have hxEpigraph :
        (x, (epigraphClosureInf φ x).toReal) ∈
          epigraph (S := (Set.univ : Set (Fin m → ℝ))) (epigraphClosureInf φ) := by
      exact
        (mem_epigraph_univ_iff (f := epigraphClosureInf φ)).2
          (EReal.le_coe_toReal htop)
    have hleToReal :
        g x ≤ (epigraphClosureInf φ x).toReal := by
      exact (mem_epigraph_univ_iff (f := g)).1 (hsubset hxEpigraph)
    have hcoe :
        (((epigraphClosureInf φ x).toReal : ℝ) : EReal) = epigraphClosureInf φ x :=
      EReal.coe_toReal htop hbot
    simpa [g, hcoe] using hleToReal
  -- The standard lower semicontinuous hull and the epigraph hull have the same epigraph, so they
  -- coincide pointwise.
  exact le_antisymm hEpigraphClosureLe (by simpa [g] using hLowerHullLe)

/-- Helper for Text 35.6.6: when the directional-derivative function never takes the value `⊥`,
its epigraph hull agrees with the Chapter 2 convex closure. -/
lemma helperForText_35_6_6_epigraphClosureInf_eq_convexFunctionClosure_of_no_bot
    {m : ℕ} {D : (Fin m → ℝ) → EReal}
    (hnotbot : ∀ y : Fin m → ℝ, D y ≠ (⊥ : EReal)) :
    epigraphClosureInf D = convexFunctionClosure D := by
  -- In the no-`⊥` branch, `convexFunctionClosure` is literally the lower semicontinuous hull.
  calc
    epigraphClosureInf D = lowerSemicontinuousHull D :=
      helperForText_35_6_6_epigraphClosureInf_eq_lowerSemicontinuousHull (φ := D)
    _ = convexFunctionClosure D := by
      symm
      simp [convexFunctionClosure, hnotbot]

/-- Helper for Text 35.6.6: if an improper convex function attains `⊥` and its effective domain
is dense, then the epigraph-closure hull is the constant `⊥` function. -/
lemma helperForText_35_6_6_epigraphClosureInf_eq_bot_of_dense_effectiveDomain
    {m : ℕ} {D : (Fin m → ℝ) → EReal}
    (hImproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) D)
    (hBot : ∃ y : Fin m → ℝ, D y = (⊥ : EReal))
    (hDense : closure (effectiveDomain (Set.univ : Set (Fin m → ℝ)) D) = Set.univ) :
    epigraphClosureInf D = fun _ => (⊥ : EReal) := by
  have hClosure :
      closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) D) =
        (Set.univ : Set ((Fin m → ℝ) × ℝ)) :=
    closure_epigraph_univ_of_exists_bot (f := D) hImproper hBot hDense
  funext x
  -- Once the real epigraph closure is all of `ℝ^m × ℝ`, every real height bounds the slice
  -- infimum from above, so the hull value must be `⊥`.
  apply helperForProposition_5_24_2_eq_bot_of_le_all_reals
  intro r
  have hrClosure :
      (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin m → ℝ))) D) := by
    simpa [hClosure]
  have hrEpigraph :
      (x, r) ∈ epigraph (S := (Set.univ : Set (Fin m → ℝ))) (epigraphClosureInf D) := by
    rw [closure_epigraph_eq_epigraph_sInf (f := D)]
    exact hrClosure
  exact (mem_epigraph_univ_iff (f := epigraphClosureInf D)).1 hrEpigraph

/-- Helper for Text 35.6.6: once the reflected convex slice `g` has dense effective domain, the
relative-interior transport from Theorem 23.3 forces the effective domain of its directional
derivative `y ↦ g'(x; y)` to be dense as well. -/
lemma helperForText_35_6_6_denseEffectiveDomain_of_dense_reflectedSliceDomain
    {m : ℕ} {g : (Fin m → ℝ) → EReal} {x : Fin m → ℝ}
    (hg : ConvexFunction g)
    (hx : g x ≠ (⊤ : EReal) ∧ g x ≠ (⊥ : EReal))
    (hDense :
      closure (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) = Set.univ) :
    closure (effectiveDomain (Set.univ : Set (Fin m → ℝ))
      (upperDirectionalDerivativeAt g x)) = Set.univ := by
  let domg : Set (Fin m → ℝ) := effectiveDomain (Set.univ : Set (Fin m → ℝ)) g
  let e := EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)
  let D : (Fin m → ℝ) → EReal := upperDirectionalDerivativeAt g x
  let C : Set (EuclideanSpace ℝ (Fin m)) :=
    e.symm '' domg
  have hdomgConv : Convex ℝ domg :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin m → ℝ))) (f := g) hg
  have hCconv : Convex ℝ C := by
    -- Pull convexity of `dom g` back through the Euclidean-space identification.
    simpa [C, e] using hdomgConv.linear_image e.symm.toLinearMap
  have hcl_C : closure C = Set.univ := by
    -- The dense-domain hypothesis on `g` is preserved by the Euclidean homeomorphism.
    calc
      closure C = e.symm '' closure domg := by
        simpa [C, e] using (e.symm.toHomeomorph.image_closure domg).symm
      _ = e.symm '' (Set.univ : Set (Fin m → ℝ)) := by
        simp [hDense, domg]
      _ = (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by
        ext z
        constructor
        · intro _hz
          simp
        · intro _hz
          exact ⟨e z, by simp⟩
  have hcl_ri :
      closure (euclideanRelativeInterior m C) =
        (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by
    -- Convex sets and their relative interiors have the same closure.
    simpa [hcl_C] using
      (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq m C hCconv).1
  let A : Set (Fin m → ℝ) :=
    (fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ) - x) '' euclideanRelativeInterior m C
  have hA_dense : Dense A := by
    -- Translating the dense relative interior of `dom g` produces a dense family of directions.
    have hdenseRange :
        DenseRange (fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ) - x) := by
      intro y
      refine subset_closure ?_
      refine ⟨(EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)).symm (y + x), ?_⟩
      simp
    have hcont :
        Continuous (fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ) - x) := by
      simpa using
        ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)).continuous.sub continuous_const)
    have hri_dense : Dense (euclideanRelativeInterior m C) := by
      intro z
      simpa [hcl_ri]
    simpa [A] using
      (DenseRange.dense_image
        (f := fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ) - x)
        hdenseRange hcont hri_dense)
  have hA_subset :
      A ⊆ effectiveDomain (Set.univ : Set (Fin m → ℝ)) D := by
    intro y hy
    rcases hy with ⟨z, hzri, rfl⟩
    have hzriFin :
        (z : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m domg := by
      -- Convert the Euclidean-space relative-interior point back to the `Fin m → ℝ` model.
      exact
        (mem_euclideanRelativeInterior_fin_iff (n := m) (C := domg) (x := (z : Fin m → ℝ))).2
          (by simpa [C, e] using hzri)
    have hzriD :
        ((z : Fin m → ℝ) - x) ∈
          euclideanRelativeInterior_fin m
            (effectiveDomain (Set.univ : Set (Fin m → ℝ)) D) := by
      -- Theorem 23.3 transports relative-interior domain points of `g` to relative-interior
      -- directions of `D`.
      simpa [D, domg] using
        helperForTheorem_23_3_directionToRi_mem_ri_effectiveDomain_directionalDerivative
          g hg x (z : Fin m → ℝ) hx hzriFin
    have hzriDE :
        e.symm ((z : Fin m → ℝ) - x) ∈
          euclideanRelativeInterior m
            (e.symm '' effectiveDomain (Set.univ : Set (Fin m → ℝ)) D) := by
      exact
        (mem_euclideanRelativeInterior_fin_iff
          (n := m) (C := effectiveDomain (Set.univ : Set (Fin m → ℝ)) D)
          (x := ((z : Fin m → ℝ) - x))).1 hzriD
    have hzmem :
        e.symm ((z : Fin m → ℝ) - x) ∈
          e.symm '' effectiveDomain (Set.univ : Set (Fin m → ℝ)) D :=
      (euclideanRelativeInterior_subset_closure m
        (e.symm '' effectiveDomain (Set.univ : Set (Fin m → ℝ)) D)).1 hzriDE
    rcases hzmem with ⟨w, hw, hwEq⟩
    have hEq : w = ((z : Fin m → ℝ) - x) := by
      apply_fun e at hwEq
      simpa [e] using hwEq
    simpa [hEq] using hw
  have hDenseDomD :
      Dense (effectiveDomain (Set.univ : Set (Fin m → ℝ)) D) :=
    Dense.mono hA_subset hA_dense
  ext y
  constructor
  · intro hy
    simp
  · intro _hy
    exact hDenseDomD y

/-- Helper for Text 35.6.6: once the reflected slice `g` has dense effective domain, the empty
subdifferential branch collapses `epigraphClosureInf (g'(x; ·))` to the constant `⊥` function. -/
lemma helperForText_35_6_6_epigraphClosureInf_eq_bot_of_empty_sliceSubdifferential_of_dense_reflectedSliceDomain
    {m : ℕ} {g : (Fin m → ℝ) → EReal} {x : Fin m → ℝ}
    (hg : ConvexFunction g)
    (hx : g x ≠ (⊤ : EReal) ∧ g x ≠ (⊥ : EReal))
    (hsubEmpty : subdifferentialAt g x = ∅)
    (hDense :
      closure (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) = Set.univ) :
    epigraphClosureInf (upperDirectionalDerivativeAt g x) = fun _ => (⊥ : EReal) := by
  let D : (Fin m → ℝ) → EReal := upperDirectionalDerivativeAt g x
  have h23Empty :=
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      g hg x hx).2 (Set.not_nonempty_iff_eq_empty.mpr hsubEmpty)
  rcases h23Empty.1 with ⟨y0, hy0Bot, _hy0Top⟩
  have hDImproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) D := by
    -- Empty subdifferential is exactly the improper branch of Theorem 23.3.
    exact
      helperForTheorem_23_3_directionalDerivative_improper_of_empty_subdifferential
        g hg x hx (Set.not_nonempty_iff_eq_empty.mpr hsubEmpty)
  have hDenseD :
      closure (effectiveDomain (Set.univ : Set (Fin m → ℝ)) D) = Set.univ :=
    helperForText_35_6_6_denseEffectiveDomain_of_dense_reflectedSliceDomain
      (g := g) (x := x) hg hx hDense
  -- The dense-domain Chapter 2 lemma now applies directly to `D`.
  exact
    helperForText_35_6_6_epigraphClosureInf_eq_bot_of_dense_effectiveDomain
      (D := D) hDImproper ⟨y0, hy0Bot⟩ hDenseD

/-- Helper for Text 35.6.6: if the reflected slice subdifferential is nonempty, then the
Chapter 2 epigraph hull of the slice directional derivative already matches the Chapter 23 support
formula. -/
lemma helperForText_35_6_6_epigraphClosureInf_eq_sliceSupport_of_nonempty_sliceSubdifferential
    {m : ℕ} {g : (Fin m → ℝ) → EReal} {x : Fin m → ℝ}
    (hg : ConvexFunction g)
    (hx : g x ≠ (⊤ : EReal) ∧ g x ≠ (⊥ : EReal))
    (hsub : Set.Nonempty (subdifferentialAt g x)) :
    epigraphClosureInf (upperDirectionalDerivativeAt g x) = subdifferentialSupportAt g x := by
  let D : (Fin m → ℝ) → EReal := upperDirectionalDerivativeAt g x
  have hclosureEq : convexFunctionClosure D = subdifferentialSupportAt g x := by
    -- Theorem 23.2 identifies the closure of the slice directional derivative with the slice
    -- support function.
    simpa [D] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg x hx (0 : Module.Dual ℝ (Fin m → ℝ))).2.2.2
  rcases hsub with ⟨xStar, hxStar⟩
  have hDnotbot : ∀ y : Fin m → ℝ, D y ≠ (⊥ : EReal) := by
    intro y hybot
    -- Any concrete subgradient gives a real lower bound, so the directional derivative cannot be
    -- `⊥` at that direction.
    have hminorant :
        ((xStar y : ℝ) : EReal) ≤ D y :=
      (((subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg x hx xStar).1).1 hxStar) y
    have hcoeBot : ((xStar y : ℝ) : EReal) = (⊥ : EReal) := by
      have hminorantBot : ((xStar y : ℝ) : EReal) ≤ (⊥ : EReal) := by
        simpa [hybot] using hminorant
      exact le_antisymm hminorantBot bot_le
    exact (EReal.coe_ne_bot (xStar y)) hcoeBot
  calc
    epigraphClosureInf D = convexFunctionClosure D :=
      helperForText_35_6_6_epigraphClosureInf_eq_convexFunctionClosure_of_no_bot
        (D := D) hDnotbot
    _ = subdifferentialSupportAt g x := hclosureEq

/-- Helper for Text 35.6.6: if the reflected slice subdifferential is empty, then the Chapter 23
support function is the constant `⊥` function. -/
lemma helperForText_35_6_6_sliceSupport_eq_bot_of_empty_sliceSubdifferential
    {m : ℕ} {g : (Fin m → ℝ) → EReal} {x : Fin m → ℝ}
    (hsubEmpty : subdifferentialAt g x = ∅) :
    subdifferentialSupportAt g x = fun _ => (⊥ : EReal) := by
  funext y
  -- With no slice subgradients available, the defining support supremum is taken over `∅`.
  simp [subdifferentialSupportAt, hsubEmpty]

/-- Helper for Text 35.6.6: nonemptiness of the textbook first partial subdifferential is
equivalent to nonemptiness of the Euclidean subdifferential of the reflected slice. -/
lemma helperForText_35_6_6_partialFirst_nonempty_iff_sliceSubdifferential_nonempty
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ↔
      Set.Nonempty (subdifferentialAt (fun x => -K (-x) v) (-u)) := by
  constructor
  · rintro ⟨uStar, huStar⟩
    refine ⟨dotProductEquiv ℝ (Fin m) uStar, ?_⟩
    -- Rewrite the textbook set membership through the preimage description of the slice
    -- subdifferential.
    have hpre :
        uStar ∈
          ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt (fun x => -K (-x) v) (-u)) := by
      simpa [helperForText_35_6_6_partialFirst_eq_sliceSubdifferential (K := K) (u := u)
        (v := v)] using huStar
    simpa using hpre
  · rintro ⟨xStar, hxStar⟩
    refine ⟨(dotProductEquiv ℝ (Fin m)).symm xStar, ?_⟩
    -- Pull the Euclidean subgradient back through the dot-product equivalence.
    have hpre :
        (dotProductEquiv ℝ (Fin m)).symm xStar ∈
          ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt (fun x => -K (-x) v) (-u)) := by
      simpa using hxStar
    simpa [helperForText_35_6_6_partialFirst_eq_sliceSubdifferential (K := K) (u := u)
      (v := v)] using hpre

/-- Helper for Text 35.6.6: if `∂₁ K(u, v)` is empty, then its textbook support function is the
constant `⊥` function. -/
lemma helperForText_35_6_6_firstPartialSupport_eq_bot_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) = fun _ => (⊥ : EReal) := by
  funext u'
  -- Once `∂₁ K(u, v)` is empty, the support supremum is over `∅`, hence equals `⊥`.
  simp [supportFunctionOfSet, hpartialEmpty]

/-- Helper for Text 35.6.6: on the empty first-partial branch, identifying any candidate hull with
the textbook support function is equivalent to showing that the candidate hull is constantly `⊥`.
-/
lemma helperForText_35_6_6_eq_firstPartialSupport_iff_eq_bot_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (φ : (Fin m → ℝ) → EReal)
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    φ = supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) ↔
      φ = fun _ => (⊥ : EReal) := by
  -- Collapse the support side first; then the branch is exactly the constant-`⊥` claim.
  rw [helperForText_35_6_6_firstPartialSupport_eq_bot_of_empty_partialFirst
    (K := K) (u := u) (v := v) hpartialEmpty]

/-- Helper for Text 35.6.6: Theorem 23.2 identifies the convex closure of the textbook
first-variable directional derivative with the support function of `∂₁ K(u, v)`. This is the
mathematically correct closure statement available even before comparing with the stronger
lower-semicontinuous hull used later in the textbook phrasing. -/
lemma helperForText_35_6_6_convexFunctionClosure_eq_firstPartialSupport
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    convexFunctionClosure (firstVariableDirectionalDerivativeFunction K u v) =
      supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) := by
  let g : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  have hg : ConvexFunction g := by
    -- Reuse the dedicated reflected-slice convexity helper from the main textbook route.
    simpa [g] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hSaddle v
  have hgu : g (-u) ≠ (⊤ : EReal) ∧ g (-u) ≠ (⊥ : EReal) := by
    -- Recentring preserves the finite base value via the reflected-base helper.
    simpa [g] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase (K := K) (u := u) (v := v) hFinite
  have hphiEq :
      firstVariableDirectionalDerivativeFunction K u v =
        upperDirectionalDerivativeAt g (-u) := by
    -- The whole directional-derivative function is already identified by the recentering helper.
    simpa [g] using
      helperForText_35_6_6_firstVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  calc
    convexFunctionClosure (firstVariableDirectionalDerivativeFunction K u v) =
        convexFunctionClosure (upperDirectionalDerivativeAt g (-u)) := by
      rw [hphiEq]
    _ = subdifferentialSupportAt g (-u) := by
      -- This is the precise closure/support identity provided by Theorem 23.2.
      simpa using
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          g hg (-u) hgu (0 : Module.Dual ℝ (Fin m → ℝ))).2.2.2
    _ = supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) := by
      -- Translate the reflected-slice support back to textbook first-partial coordinates.
      simpa [g] using
        helperForText_35_6_6_sliceSupport_eq_firstPartialSupport
          (K := K) (u := u) (v := v)

/-- Helper for Text 35.6.6: when `∂₁ K(u, v)` is empty, the correct Chapter 23 conclusion is that
the convex closure of the textbook directional-derivative function is constantly `⊥`. This does
not by itself imply the stronger `epigraphClosureInf` endpoint used in the remaining blocked
branch. -/
lemma helperForText_35_6_6_convexFunctionClosure_eq_bot_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    convexFunctionClosure (firstVariableDirectionalDerivativeFunction K u v) =
      fun _ => (⊥ : EReal) := by
  -- First rewrite the Chapter 23 closure to the textbook support function.
  calc
    convexFunctionClosure (firstVariableDirectionalDerivativeFunction K u v) =
        supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) := by
      exact
        helperForText_35_6_6_convexFunctionClosure_eq_firstPartialSupport
          (K := K) hSaddle (u := u) (v := v) hFinite
    _ = fun _ => (⊥ : EReal) := by
      -- Once `∂₁ K(u, v)` is empty, the support side collapses to the constant `⊥` function.
      exact
        helperForText_35_6_6_firstPartialSupport_eq_bot_of_empty_partialFirst
          (K := K) (u := u) (v := v) hpartialEmpty
end Section35
end Chap07
