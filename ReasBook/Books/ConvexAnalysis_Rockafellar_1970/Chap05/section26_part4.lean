/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part3

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- The sequence formulation of the boundary blow-up clause in essential smoothness for a chosen
gradient map `grad` on `int (dom f)`. -/
def HasBoundaryGradientNormBlowup {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (grad : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  ∀ (xSeq : ℕ → Fin n → ℝ) (x : Fin n → ℝ),
    (∀ i : ℕ, xSeq i ∈ C) →
    Filter.Tendsto xSeq Filter.atTop (nhds x) →
    x ∈ frontier C →
    Filter.Tendsto (fun i : ℕ => ‖grad (xSeq i)‖) Filter.atTop Filter.atTop

/-- The boundary-ray formulation of essential smoothness requiring the directional derivative
along the segment from a boundary point `x` toward any interior point `a` to tend to `-∞`
as the segment parameter tends to `0` from the right. -/
def HasBoundaryRayDirectionalDerivativeNegInfinity {n : ℕ}
    (f : (Fin n → ℝ) → EReal) : Prop :=
  let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  ∀ ⦃a x : Fin n → ℝ⦄, a ∈ C → x ∈ frontier C →
    Filter.Tendsto
      (fun t : ℝ => upperDirectionalDerivativeAt f (x + t • (a - x)) (a - x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (⊥ : EReal))

/-- Helper for Lemma 26.2: after vectorizing the covectors in `∂ f`, cyclic monotonicity of the
subdifferential becomes the usual Euclidean monotonicity inequality. -/
lemma helperForLemma_26_2_preimageSubdifferential_monotone
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x₀ x₁ v₀ v₁ : Fin n → ℝ}
    (hv₀ : v₀ ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x₀))
    (hv₁ : v₁ ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x₁)) :
    0 ≤ dotProduct (x₁ - x₀) (v₁ - v₀) := by
  -- Package Rockafellar's subdifferential as a cyclically monotone vector-valued map.
  have hcyclic :
      IsCyclicallyMonotone
        (fun x => ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) :=
    properConvexFunctionOn_isCyclicallyMonotone_subdifferential f hproper
  have hcycle := hcyclic 1 ![x₀, x₁] ![v₀, v₁] (by
    intro i
    fin_cases i
    · simpa using hv₀
    · simpa using hv₁)
  have hraw :
      dotProduct x₁ v₀ + dotProduct x₀ v₁ ≤ dotProduct x₀ v₀ + dotProduct x₁ v₁ := by
    simpa using hcycle
  have hle :
      dotProduct (x₁ - x₀) v₀ ≤ dotProduct (x₁ - x₀) v₁ := by
    have hdiff :
        dotProduct x₁ v₀ - dotProduct x₀ v₀ ≤ dotProduct x₁ v₁ - dotProduct x₀ v₁ := by
      linarith
    simpa [dotProduct_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff
  -- Rewriting the affine comparison isolates the monotonicity pairing.
  simpa [dotProduct_sub] using hle

/-- Helper for Lemma 26.2: every strict point on the segment from a boundary point of
`int (dom f)` to an interior point stays in `int (dom f)`. -/
lemma helperForLemma_26_2_segmentPoint_mem_interior
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hC_nonempty :
      (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)).Nonempty)
    {a x : Fin n → ℝ}
    (ha : a ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hx : x ∈ frontier (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)))
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    x + t • (a - x) ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
  let domf : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv : Convex ℝ domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hfConv
  have hxClosure : x ∈ closure domf := by
    -- The frontier point lies in the closure of the ambient effective domain.
    rw [← hdomConv.closure_interior_eq_closure_of_nonempty_interior hC_nonempty]
    exact hx.1
  have hcombo :
      t • a + (1 - t) • x ∈ interior domf :=
    hdomConv.combo_interior_closure_mem_interior ha hxClosure ht₀ (by linarith) (by ring)
  -- Rewrite the affine combination into the ray parameterization used in the textbook.
  convert hcombo using 1
  ext i
  simp
  ring

/-- Helper for Lemma 26.2: at an interior point with a unique Euclidean subgradient, the upper
directional derivative is exactly the dot product with that gradient. -/
lemma helperForLemma_26_2_directionalDerivative_eq_dot_grad
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {grad : (Fin n → ℝ) → (Fin n → ℝ)}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hgradMem :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x)
    (hgradUnique :
      ∀ ⦃x xStar⦄,
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x)
    {z : Fin n → ℝ}
    (hz : z ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (u : Fin n → ℝ) :
    upperDirectionalDerivativeAt f z u = (((dotProduct (grad z) u : ℝ) : ℝ) : EReal) := by
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hzFinite : f z ≠ ⊤ ∧ f z ≠ ⊥ := by
    constructor
    · exact
        mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (interior_subset hz)
    · exact hproper.2.2 z (by simp)
  have huniq :
      ∃! g : Fin n → ℝ, IsSubgradientAt f z (dotProductEquiv ℝ (Fin n) g) := by
    refine ⟨grad z, ?_, ?_⟩
    · simpa using hgradMem z hz
    · intro g hg
      exact hgradUnique hz (by simpa using hg)
  rcases
      helperForTheorem_25_1_uniqueSubgradient_implies_linearDirectionalDerivative
        (hf := hfConv) (x := z) hzFinite huniq with
    ⟨g, _hproper', hzInt, hdir⟩
  have hgSub :
      dotProductEquiv ℝ (Fin n) g ∈ subdifferentialAt f z := by
    -- The recovered linear derivative formula reconstructs the same supporting covector.
    exact
      helperForTheorem_25_1_subgradient_of_linearDirectionalDerivative
        (hproper := hproper) (hxInt := hzInt) (g := g) hdir
  have hgEq : g = grad z := hgradUnique hz hgSub
  simpa [hgEq] using hdir u

/-- Helper for Lemma 26.2: a proper convex function on all of `ℝⁿ` is, equivalently for the
Chapter 25 comparison lemmas, a proper convex `EReal`-valued function. -/
lemma helperForLemma_26_2_properConvexERealFunction
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ProperConvexERealFunction (F := (Fin n → ℝ)) f := by
  constructor
  · constructor
    · -- The `ProperConvexFunctionOn` hypothesis already rules out `⊥` everywhere on `univ`.
      intro x
      exact hproper.2.2 x (by simp)
    · -- Nonempty epigraph is equivalent to one finite point of `f`.
      rcases
          (nonempty_epigraph_iff_nonempty_effectiveDomain
            (S := (Set.univ : Set (Fin n → ℝ))) (f := f)).1 hproper.2.1 with
        ⟨x, hx⟩
      exact ⟨x, mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hx⟩
  · -- Specialize the Jensen inequality on `univ` to two weights summing to `1`.
    have hnotbot : ∀ x : Fin n → ℝ, f x ≠ ⊥ := by
      intro x
      exact hproper.2.2 x (by simp)
    have hjensen :=
      (convexFunctionOn_univ_iff_jensen_inequality (f := f) hnotbot).1 hproper.1
    intro x y a b ha hb hab
    let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
    let z : Fin 2 → (Fin n → ℝ) := fun i => if i = 0 then x else y
    have hw : ∀ i : Fin 2, 0 ≤ w i := by
      intro i
      fin_cases i <;> simp [w, ha, hb]
    have hsum : (∑ i : Fin 2, w i) = 1 := by
      simp [w, Fin.sum_univ_two, hab]
    have htwo := hjensen 2 w z hw hsum
    simpa [w, z, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using htwo

/-- Helper for Lemma 26.2: a uniform lower bound on the longitudinal pairing
`⟪grad (x + s (a - x)), a - x⟫` forces a uniform norm bound on the same gradients. -/
lemma helperForLemma_26_2_coordinate_bounds_from_longitudinal_lower_bound
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {grad : (Fin n → ℝ) → (Fin n → ℝ)}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hC_nonempty :
      (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)).Nonempty)
    (hgradMem :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x)
    (_hgradUnique :
      ∀ ⦃x xStar⦄,
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x)
    {a x : Fin n → ℝ}
    (ha : a ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hx : x ∈ frontier (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))) :
    ∀ d : ℝ, ∃ B : ℝ, ∀ {s : ℝ},
      0 < s →
      s < 1 →
      d ≤ dotProduct (grad (x + s • (a - x))) (a - x) →
      ‖grad (x + s • (a - x))‖ ≤ B := by
  have hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f :=
    helperForLemma_26_2_properConvexERealFunction hproper
  rcases
      helperForTheorem_25_1_exists_closedBall_subset_interior_effectiveDomain
        (f := f) ha with
    ⟨ρ, hρpos, hρsub⟩
  intro d
  let M : Fin n → ℝ := fun j =>
    let e : Fin n → ℝ := Pi.single j (1 : ℝ)
    let vPlus := grad (a + (ρ / 2) • e)
    let vMinus := grad (a - (ρ / 2) • e)
    let BPlus := (2 / ρ) * (|dotProduct (a - x) vPlus| + |d|)
    let BMinus := (2 / ρ) * (|dotProduct (a - x) vMinus| + |d|)
    max |vPlus j + BPlus| |vMinus j - BMinus|
  let B : ℝ := ∑ j : Fin n, M j
  refine ⟨B, ?_⟩
  intro s hsPos hsLt hdLower
  have hsLe : s ≤ 1 := by linarith
  have hxsuInt :
      x + s • (a - x) ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForLemma_26_2_segmentPoint_mem_interior hproper hC_nonempty ha hx hsPos hsLt
  have hqSub :
      grad (x + s • (a - x)) ∈
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (x + s • (a - x))) :=
    hgradMem _ hxsuInt
  have hM_nonneg : ∀ j : Fin n, 0 ≤ M j := by
    intro j
    -- Each coordinate bound is the maximum of two absolute-value bounds.
    simp [M]
  have hcoord :
      ∀ j : Fin n, |grad (x + s • (a - x)) j| ≤ M j := by
    intro j
    let e : Fin n → ℝ := Pi.single j (1 : ℝ)
    have hPlusBall : a + (ρ / 2) • e ∈ Metric.closedBall a ρ := by
      -- The symmetric comparison point is exactly `ρ / 2` away in the `j`-th coordinate.
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hcoordBall : ∀ k : Fin n, ‖((ρ / 2) • e) k‖ ≤ ρ := by
        intro k
        by_cases hk : k = j
        · subst hk
          have habs : |ρ| = ρ := abs_of_pos hρpos
          simp [e, habs]
          nlinarith
        · simp [e, hk, hρpos.le]
      have hρnonneg : 0 ≤ ρ := hρpos.le
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (pi_norm_le_iff_of_nonneg (x := (ρ / 2) • e) (r := ρ) hρnonneg).2 hcoordBall
    have hMinusBall : a - (ρ / 2) • e ∈ Metric.closedBall a ρ := by
      -- The same radius estimate works for the negative symmetric comparison point.
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hcoordBall : ∀ k : Fin n, ‖(-((ρ / 2) • e)) k‖ ≤ ρ := by
        intro k
        by_cases hk : k = j
        · subst hk
          have habs : |ρ| = ρ := abs_of_pos hρpos
          simp [e, habs]
          nlinarith
        · simp [e, hk, hρpos.le]
      have hρnonneg : 0 ≤ ρ := hρpos.le
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (pi_norm_le_iff_of_nonneg (x := -((ρ / 2) • e)) (r := ρ) hρnonneg).2 hcoordBall
    have hPlusInt :
        a + (ρ / 2) • e ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
      hρsub hPlusBall
    have hMinusInt :
        a - (ρ / 2) • e ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
      hρsub hMinusBall
    have hvPlusRaw :
        grad (a + (ρ / 2) • e) ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (a + (ρ / 2) • e)) :=
      hgradMem _ hPlusInt
    have hvMinusRaw :
        grad (a - (ρ / 2) • e) ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (a - (ρ / 2) • e)) :=
      hgradMem _ hMinusInt
    have hvPlus :
        grad (a + (ρ / 2) • e) ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹'
            subdifferentialAt f (x + (1 : ℝ) • (a - x) + (ρ / 2) • e)) := by
      -- Rewrite the endpoint `x + 1 • (a - x)` as `a`.
      convert hvPlusRaw using 1
      ext k
      simp [e]
    have hvMinus :
        grad (a - (ρ / 2) • e) ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹'
            subdifferentialAt f (x + (1 : ℝ) • (a - x) - (ρ / 2) • e)) := by
      -- Rewrite the same endpoint identity for the negative comparison point.
      convert hvMinusRaw using 1
      ext k
      simp [e]
    have hpair :
        grad (a - (ρ / 2) • e) j -
            ((2 / ρ) *
              (|dotProduct (a - x) (grad (a - (ρ / 2) • e))| + |d|)) ≤
          grad (x + s • (a - x)) j ∧
        grad (x + s • (a - x)) j ≤
          grad (a + (ρ / 2) • e) j +
            ((2 / ρ) *
              (|dotProduct (a - x) (grad (a + (ρ / 2) • e))| + |d|)) := by
      simpa [one_mul] using
        (helperForTheorem_25_6_coordinate_bound_from_monotoneComparison_with_endpoint_and_symmetricInteriorPoints
          (f := f) hf (x := x) (u := a - x) (t := 1) (s := s) (ρ := ρ) (d := d)
          (q := grad (x + s • (a - x))) (vPlus := grad (a + (ρ / 2) • e))
          (vMinus := grad (a - (ρ / 2) • e)) (j := j)
          hρpos hsPos hsLe hdLower hqSub (by simpa [e] using hvPlus) (by simpa [e] using hvMinus))
    rcases hpair with ⟨hlower, hupper⟩
    have hupper' :
        grad (x + s • (a - x)) j ≤ M j := by
      have hmain :
          grad (x + s • (a - x)) j ≤
            |grad (a + (ρ / 2) • e) j +
              ((2 / ρ) *
                (|dotProduct (a - x) (grad (a + (ρ / 2) • e))| + |d|))| := by
        refine le_trans hupper ?_
        exact le_abs_self _
      exact le_trans hmain (le_max_left _ _)
    have hlower' :
        -M j ≤ grad (x + s • (a - x)) j := by
      have hmax :
          |grad (a - (ρ / 2) • e) j -
              ((2 / ρ) *
                (|dotProduct (a - x) (grad (a - (ρ / 2) • e))| + |d|))| ≤ M j :=
        le_max_right _ _
      have hnegMax :
          -M j ≤
            -|grad (a - (ρ / 2) • e) j -
              ((2 / ρ) *
                (|dotProduct (a - x) (grad (a - (ρ / 2) • e))| + |d|))| := by
        exact neg_le_neg hmax
      have hnegAbs :
          -|grad (a - (ρ / 2) • e) j -
              ((2 / ρ) *
                (|dotProduct (a - x) (grad (a - (ρ / 2) • e))| + |d|))| ≤
            grad (a - (ρ / 2) • e) j -
              ((2 / ρ) *
                (|dotProduct (a - x) (grad (a - (ρ / 2) • e))| + |d|)) := by
        simpa using
          neg_abs_le
            (grad (a - (ρ / 2) • e) j -
              ((2 / ρ) *
                (|dotProduct (a - x) (grad (a - (ρ / 2) • e))| + |d|)))
      exact le_trans hnegMax (le_trans hnegAbs hlower)
    -- The pair of one-sided coordinate bounds gives the required absolute-value control.
    exact abs_le.2 ⟨hlower', hupper'⟩
  have hB_nonneg : 0 ≤ B := by
    -- Summing the nonnegative coordinate bounds gives a nonnegative global radius.
    exact Finset.sum_nonneg (fun j _ => hM_nonneg j)
  -- Bound each coordinate by the corresponding summand, then pass to the sup norm.
  refine (pi_norm_le_iff_of_nonneg (x := grad (x + s • (a - x))) (r := B) hB_nonneg).2 ?_
  intro j
  have hjM : M j ≤ B := by
    simp [B]
    exact Finset.single_le_sum (fun k _ => hM_nonneg k) (by simp)
  simpa using le_trans (hcoord j) hjM

/-- Helper for Lemma 26.2: monotone dot-product inequalities survive passage to the limit
because subtraction, multiplication, and finite summation are continuous in `ℝⁿ`. -/
lemma helperForLemma_26_2_limit_of_monotone_pairings
    {n : ℕ} {x z q g : Fin n → ℝ} {xSeq qSeq : ℕ → Fin n → ℝ}
    (hxTendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hqTendsto : Filter.Tendsto qSeq Filter.atTop (nhds q))
    (hmono :
      ∀ i : ℕ, 0 ≤ dotProduct (z - xSeq i) (g - qSeq i)) :
    0 ≤ dotProduct (z - x) (g - q) := by
  have hxDiff :
      Filter.Tendsto (fun i : ℕ => z - xSeq i) Filter.atTop (nhds (z - x)) :=
    (tendsto_const_nhds.sub hxTendsto)
  have hqDiff :
      Filter.Tendsto (fun i : ℕ => g - qSeq i) Filter.atTop (nhds (g - q)) :=
    (tendsto_const_nhds.sub hqTendsto)
  have hpairTendsto :
      Filter.Tendsto (fun i : ℕ => dotProduct (z - xSeq i) (g - qSeq i))
        Filter.atTop (nhds (dotProduct (z - x) (g - q))) := by
    -- Expand the dot product into a finite sum of coordinatewise products.
    classical
    have hcoord :
        ∀ j : Fin n,
          Filter.Tendsto
            (fun i : ℕ => (z j - xSeq i j) * (g j - qSeq i j))
            Filter.atTop (nhds ((z j - x j) * (g j - q j))) := by
      intro j
      exact
        (((continuous_apply j).tendsto _).comp hxDiff).mul
          (((continuous_apply j).tendsto _).comp hqDiff)
    have hsum :
        Filter.Tendsto
          (fun i : ℕ => ∑ j : Fin n, (z j - xSeq i j) * (g j - qSeq i j))
          Filter.atTop
          (nhds (∑ j : Fin n, (z j - x j) * (g j - q j))) := by
      refine Finset.induction ?_ ?_ (s := Finset.univ)
      · simp
      · intro a s ha hs
        simpa [Finset.sum_insert ha] using (hcoord a).add hs
    simpa [dotProduct] using hsum
  have hEventually :
      ∀ᶠ i : ℕ in Filter.atTop, dotProduct (z - xSeq i) (g - qSeq i) ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall hmono
  exact
    (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto
      hpairTendsto hEventually

/-- Helper for Lemma 26.2: if a boundary-approaching sequence has gradients converging to `q`,
then every inward ray pairing is bounded below by `⟪q, a - x⟫`. -/
lemma helperForLemma_26_2_cluster_limit_lower_bounds_ray_pairing
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {grad : (Fin n → ℝ) → (Fin n → ℝ)}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hC_nonempty :
      (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)).Nonempty)
    (hgradMem :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x)
    (_hgradUnique :
      ∀ ⦃x xStar⦄,
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x)
    {a x q : Fin n → ℝ}
    (ha : a ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hx : x ∈ frontier (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)))
    {xSeq : ℕ → Fin n → ℝ}
    (hxSeqMem :
      ∀ i : ℕ, xSeq i ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hxSeqTendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hqTendsto : Filter.Tendsto (fun i : ℕ => grad (xSeq i)) Filter.atTop (nhds q)) :
    ∀ {t : ℝ}, 0 < t → t < 1 →
      dotProduct q (a - x) ≤ dotProduct (grad (x + t • (a - x))) (a - x) := by
  intro t htPos htLt
  let z : Fin n → ℝ := x + t • (a - x)
  have hzInt :
      z ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    -- The strict segment point from the boundary to the interior stays inside the interior.
    simpa [z] using
      helperForLemma_26_2_segmentPoint_mem_interior hproper hC_nonempty ha hx htPos htLt
  have hzSub :
      grad z ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f z) :=
    hgradMem _ hzInt
  have hmono :
      ∀ i : ℕ, 0 ≤ dotProduct (z - xSeq i) (grad z - grad (xSeq i)) := by
    intro i
    -- Monotonicity compares the gradient at the fixed ray point with the varying boundary
    -- sequence gradients.
    have hxiSub :
        grad (xSeq i) ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (xSeq i)) :=
      hgradMem _ (hxSeqMem i)
    exact
      helperForLemma_26_2_preimageSubdifferential_monotone hproper
        hxiSub
        hzSub
  have hlimit :
      0 ≤ dotProduct (z - x) (grad z - q) := by
    -- Pass the pointwise monotonicity inequality to the limit.
    exact
      helperForLemma_26_2_limit_of_monotone_pairings
        (x := x) (z := z) (q := q) (g := grad z)
        (xSeq := xSeq) (qSeq := fun i : ℕ => grad (xSeq i))
        hxSeqTendsto hqTendsto hmono
  have hrewrite :
      dotProduct (z - x) (grad z - q) =
        t * (dotProduct (grad z) (a - x) - dotProduct q (a - x)) := by
    -- Rewrite the displacement from `x` to the ray point as `t • (a - x)`.
    calc
      dotProduct (z - x) (grad z - q)
          = dotProduct (t • (a - x)) (grad z - q) := by
              congr 1
              ext k
              simp [z]
      _ = t * dotProduct (a - x) (grad z - q) := by
            rw [dotProduct_comm, dotProduct_smul, dotProduct_comm]
            simp [smul_eq_mul]
      _ = t * (dotProduct (a - x) (grad z) - dotProduct (a - x) q) := by
            rw [dotProduct_sub]
      _ = t * (dotProduct (grad z) (a - x) - dotProduct q (a - x)) := by
            rw [dotProduct_comm (a - x) (grad z), dotProduct_comm (a - x) q]
  have hnonneg :
      0 ≤ dotProduct (grad z) (a - x) - dotProduct q (a - x) := by
    have hscaled : 0 ≤ t * (dotProduct (grad z) (a - x) - dotProduct q (a - x)) := by
      simpa [hrewrite] using hlimit
    have : 0 ≤ dotProduct (grad z) (a - x) - dotProduct q (a - x) := by
      by_cases htZero : t = 0
      · exact False.elim (lt_irrefl 0 (htZero ▸ htPos))
      · exact nonneg_of_mul_nonneg_right hscaled htPos
    exact this
  -- Rearranging the nonnegative difference gives the desired lower bound on the ray pairing.
  simpa [z, dotProduct_comm] using hnonneg

/-- Helper for Lemma 26.2: any positive sequence dominated by `1 / (k + 1)` converges to `0`
from the right. -/
lemma helperForLemma_26_2_smallPositiveSequence_tendsto_zeroWithin
    (tSeq : ℕ → ℝ)
    (htSeq : ∀ k : ℕ, 0 < tSeq k ∧ tSeq k < 1 / ((k : ℝ) + 1)) :
    Filter.Tendsto tSeq Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
  have hUpper :
      ∀ᶠ k : ℕ in Filter.atTop, tSeq k ≤ 1 / ((k : ℝ) + 1) :=
    Filter.Eventually.of_forall fun k => (htSeq k).2.le
  have hNonneg :
      ∀ᶠ k : ℕ in Filter.atTop, 0 ≤ tSeq k :=
    Filter.Eventually.of_forall fun k => (htSeq k).1.le
  have hZero :
      Filter.Tendsto tSeq Filter.atTop (nhds (0 : ℝ)) := by
    -- Squeezing between `0` and `1 / (k + 1)` gives the ambient convergence to `0`.
    refine squeeze_zero' hNonneg hUpper ?_
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)))
  -- Add the eventual positivity to upgrade from `𝓝 0` to the right-sided neighborhood filter.
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hZero, ?_⟩
  exact Filter.Eventually.of_forall fun k => (htSeq k).1

/-- Helper for Lemma 26.2: if the raywise directional derivatives do not converge to `-∞`, one
can extract a positive sequence `t_k ↓ 0` and a finite level `d` that the derivatives keep
revisiting from above. -/
lemma helperForLemma_26_2_exists_raySequence_of_not_tendsto_bot
    (φ : ℝ → EReal)
    (hφ :
      ¬ Filter.Tendsto φ (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (⊥ : EReal))) :
    ∃ d : ℝ, ∃ tSeq : ℕ → ℝ,
      (∀ k : ℕ, 0 < tSeq k ∧ tSeq k < 1 / ((k : ℝ) + 1)) ∧
      Filter.Tendsto tSeq Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) ∧
      ∀ k : ℕ, ((d : ℝ) : EReal) ≤ φ (tSeq k) := by
  have hFrequent :
      ∃ d : ℝ,
        ∀ s ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ∃ t ∈ s, ((d : ℝ) : EReal) ≤ φ t := by
    -- Negating `Tendsto ... (nhds ⊥)` produces one finite level visited in every right
    -- neighborhood of `0`.
    rw [EReal.tendsto_nhds_bot_iff_real] at hφ
    push_neg at hφ
    rcases hφ with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro s hs
    rw [Filter.frequently_iff] at hd
    exact hd hs
  rcases hFrequent with ⟨d, hd⟩
  let tSeq : ℕ → ℝ := fun k =>
    Classical.choose <|
      hd (Set.Ioo (0 : ℝ) (1 / ((k : ℝ) + 1))) (Ioo_mem_nhdsGT Nat.one_div_pos_of_nat)
  have htSeqSmall :
      ∀ k : ℕ, 0 < tSeq k ∧ tSeq k < 1 / ((k : ℝ) + 1) := by
    intro k
    -- Each witness is chosen inside the shrinking interval `Ioo (0, 1 / (k + 1))`.
    have hChosen :=
      Classical.choose_spec <|
        hd (Set.Ioo (0 : ℝ) (1 / ((k : ℝ) + 1))) (Ioo_mem_nhdsGT Nat.one_div_pos_of_nat)
    exact ⟨hChosen.1.1, hChosen.1.2⟩
  refine ⟨d, tSeq, htSeqSmall, ?_, ?_⟩
  · -- The shrinking interval bounds make the chosen witnesses converge to `0` from the right.
    exact helperForLemma_26_2_smallPositiveSequence_tendsto_zeroWithin tSeq htSeqSmall
  · intro k
    -- The second component of the chosen witness records the uniform finite lower bound.
    have hChosen :=
      Classical.choose_spec <|
        hd (Set.Ioo (0 : ℝ) (1 / ((k : ℝ) + 1))) (Ioo_mem_nhdsGT Nat.one_div_pos_of_nat)
    exact hChosen.2

-- Proof sketch: under the unique-subgradient hypothesis on `int (dom f)`, identify each
-- directional derivative along the segment with the pairing against the gradient at the interior
-- point `x + λ (a - x)`, then compare the resulting scalar blow-up with the norm blow-up along
-- sequences approaching boundary points.
/-- Lemma 26.2: assuming conditions (a) and (b) from the definition of essentially smooth, the
boundary norm blow-up condition (c) is equivalent to the raywise directional-derivative condition
(c'): `f'(x + λ (a - x); a - x) → -∞` as `λ ↓ 0` for every `a ∈ int (dom f)` and every boundary
point `x` of `int (dom f)`. -/
theorem boundaryGradientNormBlowup_iff_boundaryRayDirectionalDerivativeNegInfinity
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (grad : (Fin n → ℝ) → (Fin n → ℝ)) :
    let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
      C.Nonempty ∧
      (∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x) ∧
      (∀ ⦃x xStar⦄, x ∈ C →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x)) →
      (HasBoundaryGradientNormBlowup f grad ↔
        HasBoundaryRayDirectionalDerivativeNegInfinity f) := by
  dsimp
  intro hData
  rcases hData with ⟨hproper, hC_nonempty, hgradMem, hgradUnique⟩
  constructor
  · intro hBlowup
    intro a x ha hx
    let φ : ℝ → EReal :=
      fun t : ℝ => upperDirectionalDerivativeAt f (x + t • (a - x)) (a - x)
    by_contra hNoTendsto
    rcases helperForLemma_26_2_exists_raySequence_of_not_tendsto_bot φ hNoTendsto with
      ⟨d, tSeq, htSeqSmall, htSeqTendsto, hdLower⟩
    let raySeq : ℕ → Fin n → ℝ := fun k => x + tSeq k • (a - x)
    have hRaySeqMem :
        ∀ k : ℕ, raySeq k ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      intro k
      have hkLtOneDiv : tSeq k < 1 / ((k : ℝ) + 1) := (htSeqSmall k).2
      have hkOneDivLeOne : 1 / ((k : ℝ) + 1) ≤ 1 := by
        simpa using
          (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
            (show (1 : ℝ) ≤ (k : ℝ) + 1 by norm_num))
      have hkLtOne : tSeq k < 1 := lt_of_lt_of_le hkLtOneDiv hkOneDivLeOne
      -- Each extracted parameter gives a strict segment point, so the sequence stays in
      -- `int (dom f)`.
      simpa [raySeq] using
        helperForLemma_26_2_segmentPoint_mem_interior hproper hC_nonempty ha hx
          (htSeqSmall k).1 hkLtOne
    have htSeqZero :
        Filter.Tendsto tSeq Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_nhds_of_tendsto_nhdsWithin htSeqTendsto
    have hRaySeqTendsto : Filter.Tendsto raySeq Filter.atTop (nhds x) := by
      -- Composing `tSeq → 0` with the affine ray map yields a boundary-approaching primal
      -- sequence.
      have hCont : Continuous fun t : ℝ => x + t • (a - x) := by
        simpa using (continuous_const.add (continuous_id.smul continuous_const))
      simpa [raySeq] using hCont.continuousAt.tendsto.comp htSeqZero
    rcases
        helperForLemma_26_2_coordinate_bounds_from_longitudinal_lower_bound
          hproper hC_nonempty hgradMem hgradUnique ha hx d with
      ⟨B, hB⟩
    have hNormBound : ∀ k : ℕ, ‖grad (raySeq k)‖ ≤ B := by
      intro k
      have hkLtOneDiv : tSeq k < 1 / ((k : ℝ) + 1) := (htSeqSmall k).2
      have hkOneDivLeOne : 1 / ((k : ℝ) + 1) ≤ 1 := by
        simpa using
          (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
            (show (1 : ℝ) ≤ (k : ℝ) + 1 by norm_num))
      have hkLtOne : tSeq k < 1 := lt_of_lt_of_le hkLtOneDiv hkOneDivLeOne
      have hDirEq :
          φ (tSeq k) = (((dotProduct (grad (raySeq k)) (a - x) : ℝ) : ℝ) : EReal) := by
        -- Inside the domain, the upper directional derivative is the gradient pairing.
        simpa [φ, raySeq] using
          helperForLemma_26_2_directionalDerivative_eq_dot_grad
            hproper hgradMem hgradUnique (hRaySeqMem k) (a - x)
      have hLongitudinal :
          d ≤ dotProduct (grad (raySeq k)) (a - x) := by
        have hdLowerk : ((d : ℝ) : EReal) ≤ φ (tSeq k) := hdLower k
        rw [hDirEq] at hdLowerk
        exact_mod_cast hdLowerk
      exact hB (htSeqSmall k).1 hkLtOne hLongitudinal
    have hNormTendsto :
        Filter.Tendsto (fun k : ℕ => ‖grad (raySeq k)‖) Filter.atTop Filter.atTop :=
      hBlowup raySeq x hRaySeqMem hRaySeqTendsto hx
    have hEventuallyHigh :
        ∀ᶠ k : ℕ in Filter.atTop, B + 1 ≤ ‖grad (raySeq k)‖ :=
      by
        rw [Filter.tendsto_atTop] at hNormTendsto
        exact hNormTendsto (B + 1)
    have hEventuallyLow :
        ∀ᶠ k : ℕ in Filter.atTop, ‖grad (raySeq k)‖ < B + 1 :=
      Filter.Eventually.of_forall fun k => by
        linarith [hNormBound k]
    have hEventuallyFalse :
        ∀ᶠ k : ℕ in Filter.atTop, False :=
      (hEventuallyHigh.and hEventuallyLow).mono fun _k hk => (not_lt_of_ge hk.1) hk.2
    exact Filter.atTop_neBot.ne <| (Filter.eventually_false_iff_eq_bot).1 hEventuallyFalse
  · intro hRay
    intro xSeq x hxSeqMem hxSeqTendsto hx
    by_contra hNoBlowup
    have hNormNonneg : ∀ i : ℕ, 0 ≤ ‖grad (xSeq i)‖ := by
      intro i
      exact norm_nonneg (grad (xSeq i))
    rcases
        helperForTheorem_26_1_exists_strictMono_boundedSubsequence_of_not_tendsto_atTop
          (fun i : ℕ => ‖grad (xSeq i)‖) hNormNonneg hNoBlowup with
      ⟨R, _hRnonneg, φ, hφ, hφBound⟩
    have hSubseqMem :
        ∀ k : ℕ, grad (xSeq (φ k)) ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
      intro k
      -- The bounded subsequence of norms lies in one compact closed ball.
      simpa [Metric.mem_closedBall, dist_eq_norm] using hφBound k
    rcases (isCompact_closedBall (0 : Fin n → ℝ) R).tendsto_subseq hSubseqMem with
      ⟨q, _hqBall, ψ, hψ, hψTendsto⟩
    let ξ : ℕ → ℕ := φ ∘ ψ
    have hξ : StrictMono ξ := hφ.comp hψ
    have hSubseqTendsto : Filter.Tendsto (fun k : ℕ => xSeq (ξ k)) Filter.atTop (nhds x) := by
      -- Reindexing the primal sequence by a strict-mono subsequence preserves convergence to the
      -- boundary point.
      simpa [ξ, Function.comp] using hxSeqTendsto.comp hξ.tendsto_atTop
    have hC_nonempty_ray := hC_nonempty
    rcases hC_nonempty with ⟨a, ha⟩
    have hLower :
        ∀ {t : ℝ}, 0 < t → t < 1 →
          dotProduct q (a - x) ≤ dotProduct (grad (x + t • (a - x))) (a - x) := by
      -- The cluster point of the bounded gradient subsequence bounds every inward ray pairing
      -- from below.
      have hLowerRaw :
          ∀ {t : ℝ}, 0 < t → t < 1 →
            dotProduct q (a - x) ≤ dotProduct (grad (x + t • (a - x))) (a - x) :=
        helperForLemma_26_2_cluster_limit_lower_bounds_ray_pairing
          hproper hC_nonempty_ray hgradMem hgradUnique ha hx
          (xSeq := fun k : ℕ => xSeq (ξ k))
          (fun k : ℕ => hxSeqMem (ξ k))
          hSubseqTendsto
          (by simpa [ξ, Function.comp] using hψTendsto)
      intro t htPos htLt
      simpa [dotProduct_sub] using hLowerRaw htPos htLt
    have hRayAx :
        Filter.Tendsto
          (fun t : ℝ => upperDirectionalDerivativeAt f (x + t • (a - x)) (a - x))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds (⊥ : EReal)) :=
      hRay ha hx
    rw [EReal.tendsto_nhds_bot_iff_real] at hRayAx
    have hEventuallyLt :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          upperDirectionalDerivativeAt f (x + t • (a - x)) (a - x) <
            (((dotProduct q (a - x) : ℝ) : ℝ) : EReal) :=
      hRayAx (dotProduct q (a - x))
    have hEventuallyFalse :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), False :=
      (hEventuallyLt.and (Ioo_mem_nhdsGT zero_lt_one)).mono fun t ht => by
        have htPos : 0 < t := ht.2.1
        have htLtOne : t < 1 := ht.2.2
        have hzInt :
            x + t • (a - x) ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
          -- Strict ray points from the boundary remain in the interior.
          exact
            helperForLemma_26_2_segmentPoint_mem_interior
              hproper hC_nonempty_ray ha hx htPos htLtOne
        have hDirEq :
            upperDirectionalDerivativeAt f (x + t • (a - x)) (a - x) =
              (((dotProduct (grad (x + t • (a - x))) (a - x) : ℝ) : ℝ) : EReal) := by
          -- Rewrite the directional derivative at the strict segment point using the unique
          -- gradient.
          exact
            helperForLemma_26_2_directionalDerivative_eq_dot_grad
              hproper hgradMem hgradUnique hzInt (a - x)
        have hLowerEReal :
            (((dotProduct q (a - x) : ℝ) : ℝ) : EReal) ≤
              upperDirectionalDerivativeAt f (x + t • (a - x)) (a - x) := by
          have hLowerReal :
              dotProduct q (a - x) ≤ dotProduct (grad (x + t • (a - x))) (a - x) :=
            hLower htPos htLtOne
          rw [hDirEq]
          exact_mod_cast hLowerReal
        exact (not_lt_of_ge hLowerEReal) ht.1
    have hZeroClosure : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
      simp [closure_Ioi]
    haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) :=
      mem_closure_iff_nhdsWithin_neBot.1 hZeroClosure
    rcases Filter.Eventually.exists hEventuallyFalse with ⟨_t, htFalse⟩
    exact htFalse

/-- Definition 26.2.1: using mathlib's predicate `StrictConvexOn` for the first sentence, a
proper convex function `f` on `ℝ^n` is essentially strictly convex when, on every convex subset
of `dom ∂f = {x | ∂f(x) ≠ ∅}`, the real-valued restriction `x ↦ (f x).toReal` is strictly
convex. -/
def IsEssentiallyStrictlyConvex {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
    ∀ ⦃C : Set (Fin n → ℝ)⦄, C ⊆ subdifferentialEffectiveDomain f →
      Convex ℝ C →
      StrictConvexOn ℝ C (fun x => (f x).toReal)

-- Proof sketch: apply the defining strict-convexity clause to the convex set `ri (dom f)`,
-- using the inclusion `ri (dom f) ⊆ dom ∂ f` from Theorem 23.4; the warning about nonconvexity
-- of `dom ∂ f` is recorded as an existential counterexample.
/-- Text 26.2.1: Since `ri (dom f) ⊆ dom ∂ f ⊆ dom f`, an essentially strictly convex function
is strictly convex on `ri (dom f)`; moreover, the effective domain `dom ∂ f` of the
subdifferential need not be convex. -/
theorem essentiallyStrictlyConvex_strictConvexOn_relativeInterior_and_exists_nonconvex_subdifferentialEffectiveDomain :
    (∀ {n : ℕ} (f : (Fin n → ℝ) → EReal),
      IsEssentiallyStrictlyConvex f →
        StrictConvexOn ℝ
          (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
          (fun x => (f x).toReal)) ∧
      ∃ (n : ℕ) (f : (Fin n → ℝ) → EReal),
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
        ¬ Convex ℝ (subdifferentialEffectiveDomain f) := by
  constructor
  · intro n f hEss
    rcases hEss with ⟨hproper, hstrict⟩
    -- Theorem 23.4 supplies the inclusion `ri (dom f) ⊆ dom ∂ f`.
    have hriSubset :
        euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ⊆
          subdifferentialEffectiveDomain f :=
      (relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
        (f := f) hproper).1
    have hdomConv :
        Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hproper.1
    -- The relative interior of a convex set is convex, so Definition 26.2.1 applies on it.
    have hriConv :
        Convex ℝ
          (euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :=
      helperForTheorem_21_1_riFin_convex
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hdomConv
    exact hstrict hriSubset hriConv
  · -- The existential counterexample is already available from Chapter 24.
    exact exists_nonconvex_subdifferentialEffectiveDomain

end Section26
end Chap05
