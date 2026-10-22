/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part3

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- Theorem 35.3: let `C ⊆ ℝ^m` and `D ⊆ ℝ^n` be relatively open convex sets, let `T` be a
locally compact topological space, and let `K : C × D × T → ℝ` be concave in `u`, convex in `v`,
and continuous in `t` for each fixed `(u, v)`. Then `K` is jointly continuous on `C × D × T`.
The same conclusion holds if continuity in `t` is assumed only on a dense subset
`C' × D' ⊆ C × D`. -/
theorem section35_theorem35_3
    {m n : ℕ} {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → T → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : ∀ t, IsRealConcaveConvexOn C D (fun u v => K u v t)) :
    ((∀ u ∈ C, ∀ v ∈ D, Continuous fun t => K u v t) →
      ContinuousOn (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × T =>
        K p.1 p.2.1 p.2.2) (C ×ˢ (D ×ˢ (Set.univ : Set T)))) ∧
    ((∃ C' : Set (EuclideanSpace ℝ (Fin m)),
        ∃ D' : Set (EuclideanSpace ℝ (Fin n)),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ⊆ closure C' ∧
          D ⊆ closure D' ∧
          ∀ u ∈ C', ∀ v ∈ D', Continuous fun t => K u v t) →
      ContinuousOn (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × T =>
        K p.1 p.2.1 p.2.2) (C ×ˢ (D ×ˢ (Set.univ : Set T)))) := by
  constructor
  · -- The direct branch uses continuity in `t` on all of `C × D`.
    intro hCont
    exact
      helperForTheorem_35_3_fullContinuityImplication
        (hC := hC) (hD := hD) (hK := hK) hCont
  · -- The dense-subset branch uses nearby witness points together with the same Lipschitz bound.
    rintro ⟨C', D', hC'sub, hD'sub, hCclosure, hDclosure, hCont⟩
    exact
      helperForTheorem_35_3_denseContinuityImplication
        (hC := hC) (hD := hD) (hK := hK)
        hC'sub hD'sub hCclosure hDclosure hCont

-- Proof sketch: choose a countable dense family of points in the dense witness set and apply a
-- diagonal subsequence argument using boundedness of the real sequences `K i u v` at those points;
-- then invoke Theorem 35.4 for the resulting subsequence, whose pointwise limits on the dense set
-- extend to uniform convergence on each closed bounded subset of `C × D`.
/-- Helper for Theorem 35.5: reduce dense factor witnesses to countable dense sub-witnesses. -/
lemma helperForTheorem_35_5_exists_countableDenseFactors
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosure : C ⊆ closure C') (hDclosure : D ⊆ closure D') :
    ∃ C'' : Set (EuclideanSpace ℝ (Fin m)),
      ∃ D'' : Set (EuclideanSpace ℝ (Fin n)),
        C'' ⊆ C' ∧
        D'' ⊆ D' ∧
        C''.Countable ∧
        D''.Countable ∧
        C ⊆ closure C'' ∧
        D ⊆ closure D'' := by
  -- Choose countable dense subsets inside each dense factor witness.
  rcases Section10.exists_countable_subset_closure_superset (n := m) C' with
    ⟨C'', hC''sub, hC''count, hC'closure⟩
  rcases Section10.exists_countable_subset_closure_superset (n := n) D' with
    ⟨D'', hD''sub, hD''count, hD'closure⟩
  have hCclosure'' : C ⊆ closure C'' := by
    -- Density of `C'` and `C' ⊆ closure C''` force `C ⊆ closure C''`.
    intro x hxC
    have hxC' : x ∈ closure C' := hCclosure hxC
    have hmono : closure C' ⊆ closure C'' := by
      have : closure C' ⊆ closure (closure C'') := closure_mono hC'closure
      simpa [closure_closure] using this
    exact hmono hxC'
  have hDclosure'' : D ⊆ closure D'' := by
    -- The same closure chaining works in the second factor.
    intro y hyD
    have hyD' : y ∈ closure D' := hDclosure hyD
    have hmono : closure D' ⊆ closure D'' := by
      have : closure D' ⊆ closure (closure D'') := closure_mono hD'closure
      simpa [closure_closure] using this
    exact hmono hyD'
  exact ⟨C'', D'', hC''sub, hD''sub, hC''count, hD''count, hCclosure'', hDclosure''⟩

/-- Helper for Theorem 35.5: a pointwise bounded family on a countable set has a subsequence
converging at every point of that set. -/
lemma helperForTheorem_35_5_exists_subseq_tendstoOn_countableSet
    {α : Type*} {E : Set α} {f : ℕ → α → ℝ}
    (hEcount : E.Countable) (hbounded : Function.PointwiseBoundedFamilyOn f E) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      ∀ x ∈ E, ∃ l : ℝ, Filter.Tendsto (fun i => f (φ i) x) Filter.atTop (nhds l) := by
  classical
  by_cases hEempty : E = ∅
  · -- On the empty set the identity subsequence already satisfies the conclusion.
    refine ⟨id, strictMono_id, ?_⟩
    intro x hx
    simp [hEempty] at hx
  · -- Enumerate the nonempty countable set and apply the Chapter 10 diagonal argument.
    have hEnonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hEempty
    rcases hEcount.exists_eq_range hEnonempty with ⟨x, hx⟩
    have hbounded_x : ∀ j, Bornology.IsBounded (Set.range fun i : ℕ => f i (x j)) := by
      intro j
      have hxj : x j ∈ E := by simp [hx]
      exact hbounded (x j) hxj
    rcases
        Section10.exists_strictMono_subseq_pointwise_tendsto_on_countable_range
          (x := x) (f := f) hbounded_x with
      ⟨φ, hφ, hpoint_x⟩
    have hpoint_range :
        ∀ z ∈ Set.range x, ∃ l : ℝ,
          Filter.Tendsto (fun i => f (φ i) z) Filter.atTop (nhds l) :=
      Section10.pointwise_tendsto_on_countable_subset_from_range
        (f := f) (x := x) (φ := φ)
        (by
          intro j
          simpa using hpoint_x j)
    refine ⟨φ, hφ, ?_⟩
    -- Rewrite the original set as the chosen range.
    simpa [hx] using hpoint_range

/-- Helper for Theorem 35.5: pointwise boundedness on a countable dense product yields a
subsequence converging at every witness pair. -/
lemma helperForTheorem_35_5_exists_subseq_tendstoOn_countableDenseProduct
    {m n : ℕ}
    {C'' : Set (EuclideanSpace ℝ (Fin m))} {D'' : Set (EuclideanSpace ℝ (Fin n))}
    {KSeq : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC''count : C''.Countable) (hD''count : D''.Countable)
    (hbounded :
      Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (C'' ×ˢ D'')) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      ∀ u ∈ C'', ∀ v ∈ D'', ∃ l : ℝ,
        Filter.Tendsto (fun i => KSeq (φ i) u v) Filter.atTop (nhds l) := by
  -- Package the product witness as one countable set and reuse the countable-set lemma.
  rcases
      helperForTheorem_35_5_exists_subseq_tendstoOn_countableSet
        (E := C'' ×ˢ D'') (f := fun i => Function.uncurry (KSeq i))
        (hC''count.prod hD''count) hbounded with
    ⟨φ, hφ, hpoint⟩
  refine ⟨φ, hφ, ?_⟩
  intro u hu v hv
  -- Unpack the product membership back into the two-variable kernel notation.
  simpa [Function.uncurry] using hpoint (u, v) ⟨hu, hv⟩

/-- Theorem 35.5: let `C ⊆ ℝ^m` and `D ⊆ ℝ^n` be relatively open convex sets, and let
`K₁, K₂, ...` be a sequence of finite concave-convex functions on `C × D`. If there exist dense
subsets `C' ⊆ C` and `D' ⊆ D` such that the sequence `K i u v` is bounded for every
`(u, v) ∈ C' × D'`, then some subsequence converges uniformly on every closed bounded subset of
`C × D` to a finite concave-convex function `K`. -/
theorem section35_theorem35_5
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {KSeq : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hDense :
      ∃ C' : Set (EuclideanSpace ℝ (Fin m)),
        ∃ D' : Set (EuclideanSpace ℝ (Fin n)),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ⊆ closure C' ∧
          D ⊆ closure D' ∧
          Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (C' ×ˢ D')) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      ∃ K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ,
        IsRealConcaveConvexOn C D K ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
          S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
            TendstoUniformlyOn (fun i p => Function.uncurry (KSeq (φ i)) p) (Function.uncurry K)
              Filter.atTop S := by
  classical
  rcases hDense with ⟨C', D', hC'sub, hD'sub, hCclosure, hDclosure, hPointwiseBounded⟩
  -- First replace the dense witnesses by countable dense subsets, matching the textbook diagonal step.
  rcases
      helperForTheorem_35_5_exists_countableDenseFactors
        (C := C) (D := D) (C' := C') (D' := D') hCclosure hDclosure with
    ⟨C'', D'', hC''sub, hD''sub, hC''count, hD''count, hCclosure'', hDclosure''⟩
  have hC''subC : C'' ⊆ C := by
    intro u hu
    exact hC'sub (hC''sub hu)
  have hD''subD : D'' ⊆ D := by
    intro v hv
    exact hD'sub (hD''sub hv)
  have hPointwiseBounded'' :
      Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (C'' ×ˢ D'') := by
    -- Restrict the original boundedness hypothesis to the smaller countable dense product.
    intro p hp
    exact hPointwiseBounded p ⟨hC''sub hp.1, hD''sub hp.2⟩
  -- Next extract a diagonal subsequence converging at every point of the countable dense product.
  rcases
      helperForTheorem_35_5_exists_subseq_tendstoOn_countableDenseProduct
        (C'' := C'') (D'' := D'') (KSeq := KSeq)
        hC''count hD''count hPointwiseBounded'' with
    ⟨φ, hφ, hDenseTendsto⟩
  -- Feed the subsequence into Theorem 35.4 to upgrade dense-pointwise convergence to uniform convergence.
  rcases
      section35_theorem35_4
        (C := C) (D := D) (KSeq := fun i u v => KSeq (φ i) u v)
        hC hD (fun i => hKSeq (φ i))
        ⟨C'', D'', hC''subC, hD''subD, hCclosure'', hDclosure'', hDenseTendsto⟩ with
    ⟨K, hK, hKtendsto, hUniform⟩
  refine ⟨φ, hφ, K, hK, ?_⟩
  intro S hSsub hSclosed hSbdd
  -- Theorem 35.4 already yields the desired uniform convergence for the extracted subsequence.
  simpa [Function.uncurry] using hUniform S hSsub hSclosed hSbdd

/-- An extended-real saddle function is concave in its first variable and convex in its second
variable on `ℝ × ℝ`. -/
abbrev IsERealSaddleFunction (K : ℝ → ℝ → EReal) : Prop :=
  (∀ v : ℝ, ConvexFunction (fun u : Fin 1 → ℝ => -K (u 0) v)) ∧
    ∀ u : ℝ, ConvexFunction (fun v : Fin 1 → ℝ => K u (v 0))

/-- The directional difference quotient of an extended-real saddle function at `(u, v)` in the
direction `(u', v')`. -/
noncomputable def saddleDirectionalDifferenceQuotientAt {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : E → F → EReal) (u : E) (v : F) (u' : E) (v' : F) (t : ℝ) : EReal :=
  (K (u + t • u') (v + t • v') - K u v) / (t : EReal)

/-- Text 35.5.1: if `K` is a saddle function on `ℝ^m × ℝ^n` and is finite at `(u, v)`, then
`L` is the one-sided directional derivative of `K` at `(u, v)` with respect to `(u', v')` when
the directional difference quotient tends to `L` as `λ ↓ 0`. -/
def IsSaddleDirectionalDerivativeAt {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : E → F → EReal) (u : E) (v : F) (u' : E) (v' : F) (L : EReal) : Prop :=
  K u v ≠ (⊤ : EReal) ∧
    K u v ≠ (⊥ : EReal) ∧
    Filter.Tendsto
      (saddleDirectionalDifferenceQuotientAt K u v u' v')
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds L)

/-- The effective domain of an extended-real saddle function consists of the points where the
value is finite. -/
def saddleFunctionEffectiveDomain {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | K p.1 p.2 ≠ (⊤ : EReal) ∧ K p.1 p.2 ≠ (⊥ : EReal)}

-- Proof sketch: for fixed `v`, the slice `u ↦ -K u v` is convex because `K` is saddle. Apply
-- Theorem 23.1 to this convex slice at the finite point `u`, then negate the resulting limit to
-- recover existence of the right directional derivative of `K` in the first variable.
/-- Text 35.5.2: if `K` is a saddle function on `ℝ^m × ℝ^n` and `K u v` is finite, then for
every direction `u'` the one-sided directional derivative `K'(u, v; u', 0)` exists, i.e. the
limit of the quotients `((K (u + λ • u') v - K u v) / λ)` as `λ ↓ 0` exists. -/
theorem section35_text35_5_2
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle :
      (∀ v : Fin n → ℝ, ConvexFunction (fun u : Fin m → ℝ => -K u v)) ∧
      ∀ u : Fin m → ℝ, ConvexFunction (K u))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (u' : Fin m → ℝ) :
    ∃ L : EReal,
      Filter.Tendsto
        (fun t : ℝ => (K (u + t • u') v - K u v) / (t : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds L) := by
  let f : (Fin m → ℝ) → EReal := fun x => -K x v
  have hf : ConvexFunction f := hSaddle.1 v
  have hfu : f u ≠ (⊤ : EReal) ∧ f u ≠ (⊥ : EReal) := by
    -- Negating the finite base value preserves the finiteness needed for Theorem 23.1.
    exact ⟨by simpa [f] using hFinite.2, by simpa [f] using hFinite.1⟩
  have hfu_neBot : f u ≠ (⊥ : EReal) := hfu.2
  have hfu_neTop : f u ≠ (⊤ : EReal) := hfu.1
  have hright :
      Filter.Tendsto
        (directionalDifferenceQuotientAt f u u')
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt f u u')) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf u hfu).1 u' |>.2.1
  refine ⟨-upperDirectionalDerivativeAt f u u', ?_⟩
  have hneg :
      Filter.Tendsto
        (fun t : ℝ => -directionalDifferenceQuotientAt f u u' t)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (-upperDirectionalDerivativeAt f u u')) := by
    -- Negating the slice limit produces the candidate directional derivative for `K`.
    simpa using hright.neg
  have hEventuallyEq :
      (fun t : ℝ => (K (u + t • u') v - K u v) / (t : EReal)) =ᶠ[nhdsWithin (0 : ℝ)
        (Set.Ioi (0 : ℝ))]
        fun t : ℝ => -directionalDifferenceQuotientAt f u u' t := by
    -- Rewriting the negated convex-slice quotient recovers the target quotient for `K`.
    filter_upwards with t
    symm
    rw [directionalDifferenceQuotientAt, EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
    rw [EReal.neg_sub (Or.inr hfu_neBot) (Or.inr hfu_neTop)]
    rw [← EReal.div_eq_inv_mul]
    simp [f, sub_eq_add_neg]
  exact Filter.Tendsto.congr' hEventuallyEq.symm hneg

-- Proof sketch: for fixed `u`, the slice `v ↦ K u v` is convex because `K` is saddle. Apply
-- Theorem 23.1 to this convex slice at the finite point `v` to obtain existence of the right
-- directional derivative of `K` in the second variable.
/-- Text 35.5.3: if `K` is a saddle function on `ℝ^m × ℝ^n` and `K u v` is finite, then for
every direction `v'` the one-sided directional derivative `K'(u, v; 0, v')` exists, i.e. the
limit of the quotients `((K u (v + λ • v') - K u v) / λ)` as `λ ↓ 0` exists. -/
theorem section35_text35_5_3
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle :
      (∀ v : Fin n → ℝ, ConvexFunction (fun u : Fin m → ℝ => -K u v)) ∧
      ∀ u : Fin m → ℝ, ConvexFunction (K u))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (v' : Fin n → ℝ) :
    ∃ L : EReal,
      Filter.Tendsto
        (fun t : ℝ => (K u (v + t • v') - K u v) / (t : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds L) := by
  let f : (Fin n → ℝ) → EReal := K u
  have hf : ConvexFunction f := hSaddle.2 u
  have hright :
      Filter.Tendsto
        (directionalDifferenceQuotientAt f v v')
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt f v v')) :=
    -- The convex slice theorem gives the right directional-derivative limit in the `v`-variable.
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf v hFinite).1 v' |>.2.1
  refine ⟨upperDirectionalDerivativeAt f v v', ?_⟩
  -- Unfolding the slice quotient identifies the Chapter 23 limit with the target quotient for `K`.
  simpa [f, directionalDifferenceQuotientAt]
    using hright

/- Formalization history for Text 35.5.4: the book only observes that mixed directional
derivatives can be problematical. It does not assert the existence of a saddle-function
counterexample satisfying the specific nonexistence statement that was previously recorded here,
so that unsupported theorem has been removed. -/

-- Proof sketch: an interior point of the effective domain has an open neighborhood contained in
-- the domain. For any direction `(u', v')`, choose `δ > 0` small enough that the ray
-- `λ ↦ (u + λ • u', v + λ • v')` stays in that neighborhood for `0 ≤ λ < δ`; then the shifted
-- points remain in the effective domain, so the difference quotient is defined for all
-- sufficiently small positive `λ`.
/-- Helper for Text 35.5.5: interior membership yields an open metric ball still contained in the
effective domain. -/
lemma helperForText_35_5_5_exists_ball_subset_effectiveDomain
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (saddleFunctionEffectiveDomain K)) :
    ∃ ε > 0, Metric.ball (u, v) ε ⊆ saddleFunctionEffectiveDomain K := by
  -- Convert interior membership into a neighborhood statement at `(u, v)`.
  have hNhds : saddleFunctionEffectiveDomain K ∈ nhds (u, v) :=
    mem_interior_iff_mem_nhds.mp hInterior
  -- In a metric space, every neighborhood contains an open ball around the base point.
  exact Metric.mem_nhds_iff.mp hNhds

/-- Helper for Text 35.5.5: a sufficiently short initial segment of any ray stays inside a given
metric ball. -/
lemma helperForText_35_5_5_exists_delta_line_subset_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x w : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Set.Ico (0 : ℝ) δ, x + t • w ∈ Metric.ball x ε := by
  refine ⟨ε / (‖w‖ + 1), by positivity, ?_⟩
  intro t ht
  -- Rewrite the distance to the center as the norm of the displacement vector `t • w`.
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
  have hw_pos : 0 < ‖w‖ + 1 := by positivity
  have ht_mul : t * (‖w‖ + 1) < ε := by
    -- The choice of `δ` was made precisely so this scaled bound holds.
    exact (lt_div_iff₀ hw_pos).mp ht.2
  -- Since `0 ≤ t` and `‖w‖ ≤ ‖w‖ + 1`, the smaller norm estimate follows.
  nlinarith [norm_nonneg w, ht.1, ht_mul]

/-- Text 35.5.5: if `(u, v)` lies in the interior of the effective domain of `K`, then for every
direction `(u', v')` there exists `δ > 0` such that `(u + λ • u', v + λ • v')` remains in the
effective domain of `K` for all `λ ∈ [0, δ)`. In particular, the directional difference quotient
of `K` at `(u, v)` along `(u', v')` is well-defined for all sufficiently small `λ > 0`. -/
theorem section35_text35_5_5
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (saddleFunctionEffectiveDomain K))
    (u' : Fin m → ℝ) (v' : Fin n → ℝ) :
    ∃ δ > 0, ∀ t ∈ Set.Ico (0 : ℝ) δ,
      (u + t • u', v + t • v') ∈ saddleFunctionEffectiveDomain K := by
  -- First isolate an open ball around `(u, v)` that stays inside the effective domain.
  rcases
      helperForText_35_5_5_exists_ball_subset_effectiveDomain
        (K := K) (u := u) (v := v) hInterior with
    ⟨ε, hε, hBallSubset⟩
  -- Next choose a short initial interval along the ray that remains inside this ball.
  rcases
      helperForText_35_5_5_exists_delta_line_subset_ball
        (x := (u, v)) (w := (u', v')) hε with
    ⟨δ, hδ, hLineInBall⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  -- Combining the ray-in-ball estimate with the ball inclusion gives effective-domain membership.
  exact hBallSubset <| by
    simpa [Prod.smul_mk, Prod.mk_add_mk] using hLineInBall t ht

/-- Text 35.5.6: unless explicitly stated otherwise, the directional derivatives of `K`
considered in this section are taken at base points in the interior of the effective domain of
`K`; the directions remain arbitrary elements of `ℝ^m × ℝ^n`. -/
def section35_text35_5_6 {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  interior (saddleFunctionEffectiveDomain K)

/-- The directional difference quotient of a real-valued saddle kernel at `(u, v)` in the
direction `(u', v')`. -/
noncomputable def realSaddleDirectionalDifferenceQuotientAt {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : E → F → ℝ) (u : E) (v : F) (u' : E) (v' : F) (t : ℝ) : ℝ :=
  (K (u + t • u') (v + t • v') - K u v) / t

/-- A real-valued saddle kernel has directional derivative `L` at `(u, v)` in the direction
`(u', v')` when its right directional difference quotient converges to `L` as `t ↓ 0`. -/
def HasRealSaddleDirectionalDerivativeAt {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : E → F → ℝ) (u : E) (v : F) (u' : E) (v' : F) (L : ℝ) : Prop :=
  Filter.Tendsto
    (realSaddleDirectionalDifferenceQuotientAt K u v u' v')
    (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
    (nhds L)

/-- A bivariate real-valued kernel is jointly positively homogeneous in its two arguments if
`K (t • u') (t • v') = t * K u' v'` for every `t > 0`. -/
def IsPositivelyHomogeneousSaddleKernel {E : Type*} {F : Type*}
    [SMul ℝ E] [SMul ℝ F] (K : E → F → ℝ) : Prop :=
  ∀ u' : E, ∀ v' : F, ∀ t : ℝ, 0 < t → K (t • u') (t • v') = t * K u' v'

/-- An extended-real-valued kernel on `ℝ^m × ℝ^n` is globally concave-convex when every
`u`-slice is concave and every `v`-slice is convex on the whole space. -/
abbrev IsGloballyConcaveConvexERealKernel {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (∀ v : Fin n → ℝ,
      ConvexFunction (fun u : Fin m → ℝ => -K u v)) ∧
    ∀ u : Fin m → ℝ,
      ConvexFunction (fun v : Fin n → ℝ => K u v)

/-- Helper for Theorem 35.6: the first-variable convex slice at `v` is proper at `u`, and its
directional-derivative kernel is proper, positively homogeneous, convex, and finite in every
direction. -/
lemma helperForTheorem_35_6_firstSlice_directionalDerivativeData
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (_hD_open : IsOpen D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    let f : (Fin m → ℝ) → EReal := fun x => -K x v
    let Df : (Fin m → ℝ) → EReal := upperDirectionalDerivativeAt f u
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) Df ∧
      PositivelyHomogeneous Df ∧
      ConvexFunction Df ∧
      Df 0 = 0 ∧
      ∀ u' : Fin m → ℝ, Df u' ≠ (⊤ : EReal) ∧ Df u' ≠ (⊥ : EReal) := by
  dsimp
  let f : (Fin m → ℝ) → EReal := fun x => -K x v
  let Df : (Fin m → ℝ) → EReal := upperDirectionalDerivativeAt f u
  have hf : ConvexFunction f := hK.1 v
  have hfu : f u ≠ (⊤ : EReal) ∧ f u ≠ (⊥ : EReal) := by
    -- Negating the finite base value swaps the `⊤` and `⊥` exclusions.
    have hbase : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFinite u hu v hv
    exact ⟨by simpa [f] using hbase.2, by simpa [f] using hbase.1⟩
  have hCsubDom :
      C ⊆ effectiveDomain (Set.univ : Set (Fin m → ℝ)) f := by
    -- On the open finite patch, the negated slice never takes the value `⊤`.
    intro x hx
    have hxFinite : K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal) := hFinite x hx v hv
    simp [effectiveDomain_eq, f, lt_top_iff_ne_top, hxFinite.2]
  have huInt : u ∈ interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) := by
    -- The open set `C` sits inside the effective domain of the slice, so `u` is interior.
    refine mem_interior_iff_mem_nhds.2 ?_
    exact Filter.mem_of_superset (hC_open.mem_nhds hu) hCsubDom
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f :=
    helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
      hf huInt hfu.2
  have huRi :
      u ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
      (C := effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) huInt
  have h23 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      f hProper u
  have hDfProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) Df := by
    -- The Chapter 23 relative-interior clause makes the derivative kernel proper.
    exact (h23.2.1 huRi).2.1
  have hDfFinite :
      ∀ u' : Fin m → ℝ, Df u' ≠ (⊤ : EReal) ∧ Df u' ≠ (⊥ : EReal) :=
    h23.2.2.2 huInt
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf u hfu with
    ⟨_hdir, hDfPos, hDfConv, hDfZero, _hsymm⟩
  exact ⟨hProper, hDfProper, hDfPos, hDfConv, hDfZero, hDfFinite⟩

/-- Helper for Theorem 35.6: the second-variable convex slice at `u` is proper at `v`, and its
directional-derivative kernel is proper, positively homogeneous, convex, and finite in every
direction. -/
lemma helperForTheorem_35_6_secondSlice_directionalDerivativeData
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (_hC_open : IsOpen C) (hD_open : IsOpen D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    let g : (Fin n → ℝ) → EReal := K u
    let Dg : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt g v
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) Dg ∧
      PositivelyHomogeneous Dg ∧
      ConvexFunction Dg ∧
      Dg 0 = 0 ∧
      ∀ v' : Fin n → ℝ, Dg v' ≠ (⊤ : EReal) ∧ Dg v' ≠ (⊥ : EReal) := by
  dsimp
  let g : (Fin n → ℝ) → EReal := K u
  let Dg : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt g v
  have hg : ConvexFunction g := hK.2 u
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The slice base point is finite by the hypotheses on the open patch `C × D`.
    simpa [g] using hFinite u hu v hv
  have hDsubDom :
      D ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
    -- Finite values on `D` place the whole open patch inside the effective domain of the slice.
    intro y hy
    have hyFinite : K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal) := hFinite u hu y hy
    simp [effectiveDomain_eq, g, lt_top_iff_ne_top, hyFinite.1]
  have hvInt : v ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
    -- The open set `D` sits inside the effective domain of the slice, so `v` is interior.
    refine mem_interior_iff_mem_nhds.2 ?_
    exact Filter.mem_of_superset (hD_open.mem_nhds hv) hDsubDom
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
      hg hvInt hgv.2
  have hvRi :
      v ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
      (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) hvInt
  have h23 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      g hProper v
  have hDgProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) Dg := by
    -- The Chapter 23 relative-interior clause makes the derivative kernel proper.
    exact (h23.2.1 hvRi).2.1
  have hDgFinite :
      ∀ v' : Fin n → ℝ, Dg v' ≠ (⊤ : EReal) ∧ Dg v' ≠ (⊥ : EReal) :=
    h23.2.2.2 hvInt
  rcases convex_directionalDerivative_monotone_exists_and_sublinear g hg v hgv with
    ⟨_hdir, hDgPos, hDgConv, hDgZero, _hsymm⟩
  exact ⟨hProper, hDgProper, hDgPos, hDgConv, hDgZero, hDgFinite⟩

/-- Helper for Theorem 35.6: the textbook split kernel built from the two axis directional
derivatives is positively homogeneous, real concave-convex, and satisfies the splitting formula
`Kdir u' v' = Kdir u' 0 + Kdir 0 v'`. -/
lemma helperForTheorem_35_6_splitKernel_structure
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (_hC_conv : Convex ℝ C) (_hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    ∃ Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ,
      (∀ u' v',
        Kdir u' v' =
          -(upperDirectionalDerivativeAt (fun x => -K x v) u u').toReal +
            (upperDirectionalDerivativeAt (K u) v v').toReal) ∧
      IsPositivelyHomogeneousSaddleKernel Kdir ∧
      IsRealConcaveConvexOn (Set.univ : Set (Fin m → ℝ))
        (Set.univ : Set (Fin n → ℝ)) Kdir ∧
      ∀ u' v', Kdir u' v' = Kdir u' 0 + Kdir 0 v' := by
  rcases
      helperForTheorem_35_6_firstSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite hu hv with
    ⟨_hfProper, hDfProper, hDfPos, hDfConv, hDfZero, hDfFinite⟩
  rcases
      helperForTheorem_35_6_secondSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite hu hv with
    ⟨_hgProper, hDgProper, hDgPos, hDgConv, hDgZero, hDgFinite⟩
  let Df : (Fin m → ℝ) → EReal := upperDirectionalDerivativeAt (fun x => -K x v) u
  let Dg : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt (K u) v
  let Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ :=
    fun u' v' => -(Df u').toReal + (Dg v').toReal
  have hDfZero' : Df 0 = 0 := by
    simpa [Df] using hDfZero
  have hDgZero' : Dg 0 = 0 := by
    simpa [Dg] using hDgZero
  have hDfDom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) Df = Set.univ := by
    -- Finiteness from Theorem 23.4 makes the derivative kernel real-valued on all directions.
    ext u'
    simp [effectiveDomain_eq, Df, lt_top_iff_ne_top, (hDfFinite u').1]
  have hDgDom :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) Dg = Set.univ := by
    -- The same interior-domain finiteness holds for the second-variable derivative kernel.
    ext v'
    simp [effectiveDomain_eq, Dg, lt_top_iff_ne_top, (hDgFinite v').1]
  have hDfConvReal :
      ConvexOn ℝ (Set.univ : Set (Fin m → ℝ)) (fun u' => (Df u').toReal) := by
    -- Properness lets us pass from the `EReal` derivative kernel to a real convex function.
    simpa [hDfDom] using convexOn_toReal_effectiveDomain (f := Df) hDfProper
  have hDgConvReal :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun v' => (Dg v').toReal) := by
    -- The same `toReal` bridge applies to the second-variable derivative kernel.
    simpa [hDgDom] using convexOn_toReal_effectiveDomain (f := Dg) hDgProper
  have hFirstConcave :
      ConcaveOn ℝ (Set.univ : Set (Fin m → ℝ)) (fun u' => -(Df u').toReal) := by
    -- Negating a real convex function gives the required real concavity.
    have hNeg :
        ConvexOn ℝ (Set.univ : Set (Fin m → ℝ)) (fun u' => -(-(Df u').toReal)) := by
      simpa using hDfConvReal
    simpa using neg_convexOn_iff.mp hNeg
  have hDfScale :
      ∀ u' : Fin m → ℝ, ∀ t : ℝ, 0 < t → (Df (t • u')).toReal = t * (Df u').toReal := by
    intro u' t ht
    -- Positive homogeneity of the `EReal` derivative kernel survives after taking `toReal`.
    have hEq := congrArg EReal.toReal (hDfPos u' t ht)
    simpa [Df, EReal.toReal_mul, EReal.toReal_coe, ht.le] using hEq
  have hDgScale :
      ∀ v' : Fin n → ℝ, ∀ t : ℝ, 0 < t → (Dg (t • v')).toReal = t * (Dg v').toReal := by
    intro v' t ht
    -- The same `toReal` homogeneity holds for the second-variable derivative kernel.
    have hEq := congrArg EReal.toReal (hDgPos v' t ht)
    simpa [Dg, EReal.toReal_mul, EReal.toReal_coe, ht.le] using hEq
  refine ⟨Kdir, ?_, ?_, ?_, ?_⟩
  · -- The kernel is defined by the textbook splitting formula.
    intro u' v'
    rfl
  · intro u' v' t ht
    -- Both axis derivative kernels scale separately, so the split sum does too.
    calc
      Kdir (t • u') (t • v') =
          -(Df (t • u')).toReal + (Dg (t • v')).toReal := by
            rfl
      _ = -(t * (Df u').toReal) + t * (Dg v').toReal := by
            rw [hDfScale u' t ht, hDgScale v' t ht]
      _ = t * (-(Df u').toReal + (Dg v').toReal) := by
            ring
      _ = t * Kdir u' v' := by
            rfl
  · constructor
    · intro v' _hv'
      -- For fixed `v'`, only the first-axis term depends on `u'`, and it is concave.
      simpa [Kdir, Df, Dg, add_comm, add_left_comm, add_assoc] using
        hFirstConcave.add_const ((Dg v').toReal)
    · intro u' _hu'
      -- For fixed `u'`, only the second-axis term depends on `v'`, and it is convex.
      simpa [Kdir, Df, Dg, add_comm, add_left_comm, add_assoc] using
        hDgConvReal.add_const (-(Df u').toReal)
  · intro u' v'
    -- The zero-direction values of the two axis kernels vanish, so the split identity is exact.
    have hKdir_u0 : Kdir u' 0 = -(Df u').toReal := by
      dsimp [Kdir]
      rw [hDgZero']
      norm_num
    have hKdir_0v : Kdir 0 v' = (Dg v').toReal := by
      dsimp [Kdir]
      rw [hDfZero']
      norm_num
    calc
      Kdir u' v' = -(Df u').toReal + (Dg v').toReal := by
        rfl
      _ = Kdir u' 0 + Kdir 0 v' := by
        rw [hKdir_u0, hKdir_0v]

/-- Helper for Theorem 35.6: the split kernel from the textbook formula restricts on the axes to
the one-variable directional-derivative kernels. -/
lemma helperForTheorem_35_6_splitKernel_axisFormula
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hKdir_formula :
      ∀ u' v',
        Kdir u' v' =
          -(upperDirectionalDerivativeAt (fun x => -K x v) u u').toReal +
            (upperDirectionalDerivativeAt (K u) v v').toReal) :
    (∀ u', Kdir u' 0 = -(upperDirectionalDerivativeAt (fun x => -K x v) u u').toReal) ∧
      ∀ v', Kdir 0 v' = (upperDirectionalDerivativeAt (K u) v v').toReal := by
  rcases
      helperForTheorem_35_6_firstSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite hu hv with
    ⟨_hfProper, _hDfProper, _hDfPos, _hDfConv, hDfZero, _hDfFinite⟩
  rcases
      helperForTheorem_35_6_secondSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite hu hv with
    ⟨_hgProper, _hDgProper, _hDgPos, _hDgConv, hDgZero, _hDgFinite⟩
  constructor
  · intro u'
    -- On the first axis, the second-variable directional derivative vanishes at `0`.
    rw [hKdir_formula]
    rw [hDgZero]
    norm_num
  · intro v'
    -- On the second axis, the first-variable directional derivative vanishes at `0`.
    rw [hKdir_formula]
    rw [hDfZero]
    norm_num

/-- Helper for Theorem 35.6: the axis directional derivatives already match the split kernel, so
the remaining work in the main theorem is only the genuinely mixed-direction limit. -/
lemma helperForTheorem_35_6_axisDirectionalDerivatives_match_splitKernel
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hKdir_formula :
      ∀ u' v',
        Kdir u' v' =
          -(upperDirectionalDerivativeAt (fun x => -K x v) u u').toReal +
            (upperDirectionalDerivativeAt (K u) v v').toReal) :
    (∀ u', IsSaddleDirectionalDerivativeAt K u v u' 0 (Kdir u' 0 : EReal)) ∧
      ∀ v', IsSaddleDirectionalDerivativeAt K u v 0 v' (Kdir 0 v' : EReal) := by
  have hFiniteuv : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFinite u hu v hv
  have hAxisFormula :=
    helperForTheorem_35_6_splitKernel_axisFormula
      (C := C) (D := D) (K := K)
      hC_open hD_open hK hFinite hu hv hKdir_formula
  rcases
      helperForTheorem_35_6_firstSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite hu hv with
    ⟨_hfProper, _hDfProper, _hDfPos, _hDfConv, _hDfZero, hDfFinite⟩
  rcases
      helperForTheorem_35_6_secondSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite hu hv with
    ⟨_hgProper, _hDgProper, _hDgPos, _hDgConv, _hDgZero, hDgFinite⟩
  constructor
  · intro u'
    let f : (Fin m → ℝ) → EReal := fun x => -K x v
    have hf : ConvexFunction f := hK.1 v
    have hfu : f u ≠ (⊤ : EReal) ∧ f u ≠ (⊥ : EReal) := by
      -- Negating the finite base value swaps the `⊤` and `⊥` exclusions exactly as in Text 35.5.2.
      exact ⟨by simpa [f] using hFiniteuv.2, by simpa [f] using hFiniteuv.1⟩
    have hfu_neBot : f u ≠ (⊥ : EReal) := hfu.2
    have hfu_neTop : f u ≠ (⊤ : EReal) := hfu.1
    have hright :
        Filter.Tendsto
          (directionalDifferenceQuotientAt f u u')
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds (upperDirectionalDerivativeAt f u u')) :=
      (convex_directionalDerivative_monotone_exists_and_sublinear f hf u hfu).1 u' |>.2.1
    have hneg :
        Filter.Tendsto
          (fun t : ℝ => -directionalDifferenceQuotientAt f u u' t)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds (-upperDirectionalDerivativeAt f u u')) := by
      -- Negating the slice derivative identifies the first-axis derivative of the saddle kernel.
      simpa using hright.neg
    have hEventuallyEq :
        (fun t : ℝ => saddleDirectionalDifferenceQuotientAt K u v u' 0 t) =ᶠ[nhdsWithin (0 : ℝ)
          (Set.Ioi (0 : ℝ))]
          fun t : ℝ => -directionalDifferenceQuotientAt f u u' t := by
      -- Unfolding the mixed quotient with zero second direction recovers the one-variable slice quotient.
      filter_upwards with t
      symm
      rw [directionalDifferenceQuotientAt, saddleDirectionalDifferenceQuotientAt,
        EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
      rw [EReal.neg_sub (Or.inr hfu_neBot) (Or.inr hfu_neTop)]
      rw [← EReal.div_eq_inv_mul]
      simp [f, sub_eq_add_neg]
    have hKdirEq :
        ((Kdir u' 0 : ℝ) : EReal) = -upperDirectionalDerivativeAt f u u' := by
      have hreal : Kdir u' 0 = -(upperDirectionalDerivativeAt f u u').toReal := by
        simpa [f] using hAxisFormula.1 u'
      calc
        ((Kdir u' 0 : ℝ) : EReal) = ((-(upperDirectionalDerivativeAt f u u').toReal : ℝ) : EReal) := by
          exact congrArg (fun r : ℝ => (r : EReal)) hreal
        _ = -upperDirectionalDerivativeAt f u u' := by
          simpa using congrArg Neg.neg (EReal.coe_toReal (hDfFinite u').1 (hDfFinite u').2)
    refine ⟨hFiniteuv.1, hFiniteuv.2, ?_⟩
    -- The first-axis limit is already established, so only the target value needs to be rewritten.
    simpa [hKdirEq] using Filter.Tendsto.congr' hEventuallyEq.symm hneg
  · intro v'
    let f : (Fin n → ℝ) → EReal := K u
    have hf : ConvexFunction f := hK.2 u
    have hright :
        Filter.Tendsto
          (directionalDifferenceQuotientAt f v v')
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds (upperDirectionalDerivativeAt f v v')) :=
      (convex_directionalDerivative_monotone_exists_and_sublinear f hf v hFiniteuv).1 v' |>.2.1
    have hEventuallyEq :
        (fun t : ℝ => saddleDirectionalDifferenceQuotientAt K u v 0 v' t) =ᶠ[nhdsWithin (0 : ℝ)
          (Set.Ioi (0 : ℝ))]
          directionalDifferenceQuotientAt f v v' := by
      -- Unfolding the mixed quotient with zero first direction recovers the second-variable slice quotient.
      filter_upwards with t
      simp [directionalDifferenceQuotientAt, saddleDirectionalDifferenceQuotientAt, f]
    have hKdirEq :
        ((Kdir 0 v' : ℝ) : EReal) = upperDirectionalDerivativeAt f v v' := by
      have hreal : Kdir 0 v' = (upperDirectionalDerivativeAt f v v').toReal := by
        simpa [f] using hAxisFormula.2 v'
      calc
        ((Kdir 0 v' : ℝ) : EReal) = (((upperDirectionalDerivativeAt f v v').toReal : ℝ) : EReal) := by
          exact congrArg (fun r : ℝ => (r : EReal)) hreal
        _ = upperDirectionalDerivativeAt f v v' := by
          simpa using EReal.coe_toReal (hDgFinite v').1 (hDgFinite v').2
    refine ⟨hFiniteuv.1, hFiniteuv.2, ?_⟩
    -- The second-axis limit is the direct slice derivative from Text 35.5.3.
    simpa [hKdirEq] using Filter.Tendsto.congr' hEventuallyEq.symm hright

/-- Helper for Theorem 35.6: translating the open convex product `C × D` by `-(u, v)` yields
relatively open convex direction domains containing `0`, and every scaled direction with
`0 < t ≤ 1` stays inside the original product. -/
lemma helperForTheorem_35_6_translatedDirectionDomains
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    let CU : Set (Fin m → ℝ) := {u' | u + u' ∈ C}
    let DV : Set (Fin n → ℝ) := {v' | v + v' ∈ D}
    IsRelativelyOpenConvex CU ∧
      IsRelativelyOpenConvex DV ∧
      (0 : Fin m → ℝ) ∈ CU ∧
      (0 : Fin n → ℝ) ∈ DV ∧
      ∀ {t : ℝ}, 0 < t → t ≤ 1 →
        ∀ {u' : Fin m → ℝ} {v' : Fin n → ℝ}, u' ∈ CU → v' ∈ DV →
          u + t • u' ∈ C ∧ v + t • v' ∈ D := by
  dsimp
  have hCU_open : IsOpen ({u' : Fin m → ℝ | u + u' ∈ C} : Set (Fin m → ℝ)) := by
    -- Translating the open set `C` keeps the direction domain open in the ambient space.
    simpa using hC_open.preimage (continuous_const.add continuous_id)
  have hDV_open : IsOpen ({v' : Fin n → ℝ | v + v' ∈ D} : Set (Fin n → ℝ)) := by
    -- The same translation argument works in the second factor.
    simpa using hD_open.preimage (continuous_const.add continuous_id)
  have hCU_conv : Convex ℝ ({u' : Fin m → ℝ | u + u' ∈ C} : Set (Fin m → ℝ)) := by
    -- Convexity is preserved by translating the original set `C`.
    intro x hx y hy a b ha hb hab
    have hcombo :
        u + (a • x + b • y) = a • (u + x) + b • (u + y) := by
      ext i
      have hu_split : (a + b) * u i = u i := by
        rw [hab]
        ring
      calc
        (u + (a • x + b • y)) i = u i + (a * x i + b * y i) := by simp
        _ = (a + b) * u i + (a * x i + b * y i) := by rw [hu_split]
        _ = (a • (u + x) + b • (u + y)) i := by
              simp
              ring
    change u + (a • x + b • y) ∈ C
    rw [hcombo]
    exact hC_conv hx hy ha hb hab
  have hDV_conv : Convex ℝ ({v' : Fin n → ℝ | v + v' ∈ D} : Set (Fin n → ℝ)) := by
    -- The translated direction domain for `D` is convex for the same reason.
    intro x hx y hy a b ha hb hab
    have hcombo :
        v + (a • x + b • y) = a • (v + x) + b • (v + y) := by
      ext i
      have hv_split : (a + b) * v i = v i := by
        rw [hab]
        ring
      calc
        (v + (a • x + b • y)) i = v i + (a * x i + b * y i) := by simp
        _ = (a + b) * v i + (a * x i + b * y i) := by rw [hv_split]
        _ = (a • (v + x) + b • (v + y)) i := by
              simp
              ring
    change v + (a • x + b • y) ∈ D
    rw [hcombo]
    exact hD_conv hx hy ha hb hab
  refine ⟨⟨hCU_conv, ?_⟩, ⟨hDV_conv, ?_⟩, ?_, ?_, ?_⟩
  · -- Ambient openness pulls back to relative openness inside the affine span.
    simpa using hCU_open.preimage (continuous_subtype_val :
      Continuous fun x : affineSpan ℝ ({u' : Fin m → ℝ | u + u' ∈ C} : Set (Fin m → ℝ)) =>
        (x : Fin m → ℝ))
  · -- The same pullback argument gives relative openness for the `v`-directions.
    simpa using hDV_open.preimage (continuous_subtype_val :
      Continuous fun x : affineSpan ℝ ({v' : Fin n → ℝ | v + v' ∈ D} : Set (Fin n → ℝ)) =>
        (x : Fin n → ℝ))
  · -- Zero direction corresponds to the base point `(u, v)` itself.
    simpa using hu
  · -- Zero direction in the second factor also stays at the base point.
    simpa using hv
  · intro t ht_pos ht_le u' v' hu' hv'
    constructor
    · -- Convexity of `C` keeps the segment from `u` to `u + u'` inside `C`.
      have hrewrite :
          u + t • u' = (1 - t) • u + t • (u + u') := by
        ext i
        simp [smul_add]
        ring
      rw [hrewrite]
      exact hC_conv hu hu' (by linarith) ht_pos.le (by linarith)
    · -- The same segment argument works in the second factor.
      have hrewrite :
          v + t • v' = (1 - t) • v + t • (v + v') := by
        ext i
        simp [smul_add]
        ring
      rw [hrewrite]
      exact hD_conv hv hv' (by linarith) ht_pos.le (by linarith)

/-- Helper for Theorem 35.6: every short positive step inside the translated direction domains
lands at a finite value of `K` on the mixed point `(u + t • u', v + t • v')`. -/
lemma helperForTheorem_35_6_scaledStep_finiteValues
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    let CU : Set (Fin m → ℝ) := {u' | u + u' ∈ C}
    let DV : Set (Fin n → ℝ) := {v' | v + v' ∈ D}
    ∀ {t : ℝ}, 0 < t → t ≤ 1 →
      ∀ {u' : Fin m → ℝ} {v' : Fin n → ℝ}, u' ∈ CU → v' ∈ DV →
        K (u + t • u') (v + t • v') ≠ (⊤ : EReal) ∧
          K (u + t • u') (v + t • v') ≠ (⊥ : EReal) := by
  dsimp
  obtain ⟨_hCU, _hDV, _h0CU, _h0DV, hScaledMem⟩ :=
    helperForTheorem_35_6_translatedDirectionDomains
      (C := C) (D := D) hC_open hD_open hC_conv hD_conv hu hv
  intro t ht_pos ht_le u' v' hu' hv'
  -- First use the translated-domain geometry to keep the scaled point inside `C × D`.
  obtain ⟨huScaled, hvScaled⟩ := hScaledMem ht_pos ht_le hu' hv'
  -- Then the finiteness hypothesis on the open patch applies directly at that scaled point.
  exact hFinite (u + t • u') huScaled (v + t • v') hvScaled

/-- Helper for Theorem 35.6: the same short positive steps also keep the one-variable slice
points `(u + t • u', v)` and `(u, v + t • v')` inside the finite patch `C × D`. -/
lemma helperForTheorem_35_6_scaledAxisStep_finiteValues
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    let CU : Set (Fin m → ℝ) := {u' | u + u' ∈ C}
    let DV : Set (Fin n → ℝ) := {v' | v + v' ∈ D}
    ∀ {t : ℝ}, 0 < t → t ≤ 1 →
      ∀ {u' : Fin m → ℝ} {v' : Fin n → ℝ}, u' ∈ CU → v' ∈ DV →
        (K (u + t • u') v ≠ (⊤ : EReal) ∧ K (u + t • u') v ≠ (⊥ : EReal)) ∧
          (K u (v + t • v') ≠ (⊤ : EReal) ∧ K u (v + t • v') ≠ (⊥ : EReal)) := by
  dsimp
  obtain ⟨_hCU, _hDV, h0CU, h0DV, hScaledMem⟩ :=
    helperForTheorem_35_6_translatedDirectionDomains
      (C := C) (D := D) hC_open hD_open hC_conv hD_conv hu hv
  intro t ht_pos ht_le u' v' hu' hv'
  -- Apply the translated-domain step lemma once with zero `v`-direction and once with zero
  -- `u`-direction to recover the two axis slices used in the quotient decomposition.
  have hFirstStep : u + t • u' ∈ C ∧ v + t • (0 : Fin n → ℝ) ∈ D :=
    hScaledMem ht_pos ht_le hu' h0DV
  have hSecondStep : u + t • (0 : Fin m → ℝ) ∈ C ∧ v + t • v' ∈ D :=
    hScaledMem ht_pos ht_le h0CU hv'
  constructor
  · -- The moved first slice stays in `C × D`.
    simpa using hFinite (u + t • u') hFirstStep.1 v (by simpa using hFirstStep.2)
  · -- The moved second slice stays in `C × D`.
    simpa using hFinite u (by simpa using hSecondStep.1) (v + t • v') hSecondStep.2


end Section35
end Chap07
