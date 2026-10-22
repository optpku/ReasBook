/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part12

section Chap06
section Section27

attribute [local instance] Classical.propDecidable

-- Proof sketch: apply Theorem 6.27.2 to get a bounded minimum set and quantitative proximity of
-- sufficiently near-minimizers to that set. Since `f (xSeq i) → inf f`, the tail of the sequence
-- eventually lies in an arbitrarily small neighborhood of the bounded minimum set, which makes
-- the whole sequence bounded. Any cluster point is then a limit of near-minimizers approaching the
-- closed minimum set, so closedness forces that cluster point to belong to the minimum set.
/-- Helper for Corollary 6.27.1: a sequence whose values tend to `inf f` is eventually arbitrarily
close to the minimum set once Theorem 6.27.2 provides the quantitative near-minimizer estimate. -/
lemma helperForCorollary_6_27_1_eventually_exists_nearby_minimizer {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (xSeq : ℕ → (Fin n → ℝ))
    (hInfFinite : IsFiniteEReal (functionInfimumEReal f))
    (hnearby :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x : Fin n → ℝ,
            f x ≤ functionInfimumEReal f + (δ : EReal) →
              ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - x‖ < ε)
    (hnearMin :
      Filter.Tendsto (fun i : ℕ => f (xSeq i)) Filter.atTop (nhds (functionInfimumEReal f))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i : ℕ in Filter.atTop,
        ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - xSeq i‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hnearby ε hε
  have hInf_coe :
      (((functionInfimumEReal f).toReal : ℝ) : EReal) = functionInfimumEReal f := by
    simpa using (EReal.coe_toReal (x := functionInfimumEReal f) hInfFinite.1 hInfFinite.2)
  -- Move from convergence to `inf f` to eventual membership in the strict sublevel `inf f + δ`.
  have hlt :
      functionInfimumEReal f < functionInfimumEReal f + (δ : EReal) := by
    have hltReal :
        (functionInfimumEReal f).toReal < (functionInfimumEReal f).toReal + δ := by
      linarith
    have hltE :
        ((((functionInfimumEReal f).toReal : ℝ) : EReal)) <
          ((((functionInfimumEReal f).toReal + δ : ℝ) : EReal)) := by
      exact EReal.coe_lt_coe_iff.2 hltReal
    simpa [hInf_coe, add_assoc, add_left_comm, add_comm] using hltE
  have hEventuallyLt :
      ∀ᶠ i : ℕ in Filter.atTop, f (xSeq i) < functionInfimumEReal f + (δ : EReal) := by
    simpa using hnearMin (Iio_mem_nhds hlt)
  -- On that tail, the quantitative estimate from Theorem 6.27.2 gives a nearby minimizer.
  filter_upwards [hEventuallyLt] with i hi
  exact hδ (xSeq i) (le_of_lt hi)

/-- Helper for Corollary 6.27.1: eventual unit proximity to a bounded minimum set bounds the whole
sequence. -/
lemma helperForCorollary_6_27_1_bounded_range_of_eventually_unit_close_to_minimizers {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (xSeq : ℕ → (Fin n → ℝ))
    (hMinBounded : Bornology.IsBounded (minimumSetEReal f))
    (hnear :
      ∀ᶠ i : ℕ in Filter.atTop,
        ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - xSeq i‖ < 1) :
    Bornology.IsBounded (Set.range xSeq) := by
  rcases hMinBounded.exists_pos_norm_le with ⟨R, _hRpos, hR⟩
  rcases Filter.eventually_atTop.mp hnear with ⟨N, hN⟩
  have hheadFinite : (xSeq '' Set.Iic N).Finite := (Set.finite_Iic N).image xSeq
  have hheadBounded : Bornology.IsBounded (xSeq '' Set.Iic N) := hheadFinite.isBounded
  -- A point within distance `1` of a bounded minimum set lies in a fixed closed ball.
  have htailSubset : xSeq '' Set.Ici N ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
    intro y hy
    rcases hy with ⟨i, hiN, rfl⟩
    rcases hN i hiN with ⟨z, hzMin, hzClose⟩
    have hzNorm : ‖z‖ ≤ R := hR z hzMin
    have hzClose' : ‖xSeq i - z‖ < 1 := by
      simpa [norm_sub_rev] using hzClose
    have hxNorm : ‖xSeq i‖ < R + 1 := by
      calc
        ‖xSeq i‖ = ‖(xSeq i - z) + z‖ := by simp
        _ ≤ ‖xSeq i - z‖ + ‖z‖ := norm_add_le _ _
        _ < 1 + R := add_lt_add_of_lt_of_le hzClose' hzNorm
        _ = R + 1 := by ring
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hxNorm
  have htailBounded : Bornology.IsBounded (Metric.closedBall (0 : Fin n → ℝ) (R + 1)) :=
    Metric.isBounded_closedBall
  -- Split the range into the finite head and the uniformly bounded tail.
  have hrangeSubset :
      Set.range xSeq ⊆ xSeq '' Set.Iic N ∪ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
    intro y hy
    rcases hy with ⟨i, rfl⟩
    by_cases hiN : N ≤ i
    · exact Or.inr (htailSubset ⟨i, hiN, rfl⟩)
    · exact Or.inl ⟨i, Nat.le_of_lt (Nat.lt_of_not_ge hiN), rfl⟩
  exact (hheadBounded.union htailBounded).subset hrangeSubset

/-- Helper for Corollary 6.27.1: a cluster point of a sequence that is eventually arbitrarily
close to the closed minimum set must itself belong to that minimum set. -/
lemma helperForCorollary_6_27_1_clusterPoint_mem_minimumSet_of_eventual_proximity {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (xSeq : ℕ → (Fin n → ℝ))
    (hMinClosed : IsClosed (minimumSetEReal f))
    (hnear :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ i : ℕ in Filter.atTop,
          ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - xSeq i‖ < ε) :
    ∀ x : Fin n → ℝ, MapClusterPt x Filter.atTop xSeq → x ∈ minimumSetEReal f := by
  intro x hxCluster
  -- Frequent visits near a cluster point combine with eventual proximity to the minimum set.
  have hxClosure : x ∈ closure (minimumSetEReal f) := by
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    have hεhalf : 0 < ε / 2 := by
      linarith
    have hfreqBall :
        ∃ᶠ i : ℕ in Filter.atTop, xSeq i ∈ Metric.ball x (ε / 2) :=
      hxCluster.frequently (Metric.ball_mem_nhds x hεhalf)
    have hnearHalf :
        ∀ᶠ i : ℕ in Filter.atTop,
          ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - xSeq i‖ < ε / 2 :=
      hnear (ε / 2) hεhalf
    obtain ⟨i, hiBall, hiNear⟩ := (hfreqBall.and_eventually hnearHalf).exists
    rcases hiNear with ⟨z, hzMin, hzClose⟩
    have hDistBall : dist (xSeq i) x < ε / 2 := Metric.mem_ball.mp hiBall
    have hDistClose : dist z (xSeq i) < ε / 2 := by
      simpa [dist_eq_norm] using hzClose
    have hDistBall' : dist x (xSeq i) < ε / 2 := by
      simpa [dist_comm] using hDistBall
    have hDistClose' : dist (xSeq i) z < ε / 2 := by
      simpa [dist_comm] using hDistClose
    refine ⟨z, hzMin, ?_⟩
    calc
      dist x z ≤ dist x (xSeq i) + dist (xSeq i) z := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hDistBall' hDistClose'
      _ = ε := by ring
  simpa [hMinClosed.closure_eq] using hxClosure

/-- Corollary 6.27.1: if `f` is a closed proper convex function with no recession directions and
`xSeq` is a sequence with `f (xSeq i) → inf f`, then `xSeq` is bounded and every cluster point of
`xSeq` belongs to the minimum set of `f`. -/
theorem nearMinimizingSequence_bounded_and_clusterPoints_mem_minimumSet_of_noRecessionDirections
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hnoRecession : HasNoRecessionDirections f) (xSeq : ℕ → (Fin n → ℝ))
    (hnearMin :
      Filter.Tendsto (fun i : ℕ => f (xSeq i)) Filter.atTop (nhds (functionInfimumEReal f))) :
    Bornology.IsBounded (Set.range xSeq) ∧
      ∀ x : Fin n → ℝ, MapClusterPt x Filter.atTop xSeq → x ∈ minimumSetEReal f := by
  rcases
      closedProperConvexFunction_near_minimizer_of_noRecessionDirections
        f hclosed hproper hnoRecession with
    ⟨hInfFinite, _hMinNonempty, hMinClosed, hMinBounded, _hMinConvex, hnearby⟩
  have hEventuallyNear :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ i : ℕ in Filter.atTop,
          ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - xSeq i‖ < ε :=
    helperForCorollary_6_27_1_eventually_exists_nearby_minimizer
      (f := f) (xSeq := xSeq) hInfFinite hnearby hnearMin
  -- First, specialize the eventual proximity estimate at radius `1` to bound the whole range.
  have hBounded : Bornology.IsBounded (Set.range xSeq) :=
    helperForCorollary_6_27_1_bounded_range_of_eventually_unit_close_to_minimizers
      (f := f) (xSeq := xSeq) hMinBounded (hEventuallyNear 1 (by norm_num))
  refine ⟨hBounded, ?_⟩
  -- Then every cluster point lies in the closure of the minimum set, hence in the closed set.
  exact
    helperForCorollary_6_27_1_clusterPoint_mem_minimumSet_of_eventual_proximity
      (f := f) (xSeq := xSeq) hMinClosed hEventuallyNear

/-- Helper for Corollary 6.27.2: a singleton minimum set yields no recession directions via part
(d) of Theorem 6.27.1. -/
lemma helperForCorollary_6_27_2_hasNoRecessionDirections_of_singleton_minimumSet
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hmin : minimumSetEReal f = ({x} : Set (Fin n → ℝ))) :
    HasNoRecessionDirections f := by
  rcases closedProperConvexFunction_minimum_characterizations f hclosed hproper with
    ⟨_hA, _hB, _hC, hD, _hE, _hF, _hG, _hH, _hI⟩
  have hMinNonemptyBounded :
      (minimumSetEReal f).Nonempty ∧ Bornology.IsBounded (minimumSetEReal f) := by
    constructor
    · -- The singleton hypothesis immediately provides a minimizer.
      refine ⟨x, ?_⟩
      simp [hmin]
    · -- A singleton set is bounded, so the minimum set is bounded after rewriting.
      rw [hmin]
      exact (Bornology.isBounded_singleton : Bornology.IsBounded ({x} : Set (Fin n → ℝ)))
  -- Part (d) converts nonempty bounded minimum set into absence of recession directions.
  exact hD.2.1 (hD.1.1 hMinNonemptyBounded)

/-- Helper for Corollary 6.27.2: once every cluster point belongs to the singleton minimum set,
that cluster point must equal the minimizer. -/
lemma helperForCorollary_6_27_2_unique_clusterPoint {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hmin : minimumSetEReal f = ({x} : Set (Fin n → ℝ)))
    (xSeq : ℕ → (Fin n → ℝ))
    (hclusterInMin :
      ∀ y : Fin n → ℝ, MapClusterPt y Filter.atTop xSeq → y ∈ minimumSetEReal f) :
    ∀ y : Fin n → ℝ, MapClusterPt y Filter.atTop xSeq → y = x := by
  intro y hy
  -- Rewrite cluster-point membership in the minimum set using the singleton hypothesis.
  have hyMin : y ∈ minimumSetEReal f := hclusterInMin y hy
  rw [hmin] at hyMin
  simpa using hyMin

/-- Helper for Corollary 6.27.2: a bounded sequence is eventually contained in one closed ball,
which provides the compact carrier needed for the unique-cluster-point convergence criterion. -/
lemma helperForCorollary_6_27_2_closedBall_eventually_contains_sequence {n : ℕ}
    (xSeq : ℕ → (Fin n → ℝ))
    (hBounded : Bornology.IsBounded (Set.range xSeq)) :
    ∃ R : ℝ, 0 < R ∧
      ∀ᶠ i : ℕ in Filter.atTop, xSeq i ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
  rcases hBounded.exists_pos_norm_le with ⟨R, hRpos, hR⟩
  refine ⟨R, hRpos, ?_⟩
  -- The uniform norm bound places every sequence term in the same closed ball.
  refine Filter.Eventually.of_forall ?_
  intro i
  simpa [Metric.mem_closedBall, dist_eq_norm] using hR (xSeq i) ⟨i, rfl⟩

-- Proof sketch: first use the singleton minimum-set hypothesis to know that `x` is the only
-- cluster point permitted by Corollary 6.27.1. That earlier corollary also gives boundedness of
-- the sequence, and in finite-dimensional Euclidean space a bounded sequence with a unique cluster
-- point must converge to that point.
/-- Corollary 6.27.2: let `f` be a closed proper convex function whose minimum set is the singleton
`{x}`. If `xSeq` is any sequence such that `f (xSeq i)` tends to `inf f`, then `xSeq` tends to
`x`. This formalizes the statement that a closed proper convex function attaining its infimum at a
unique point forces every near-minimizing sequence to converge to that unique minimizer. -/
theorem nearMinimizingSequence_tendsto_of_unique_minimizer
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hmin : minimumSetEReal f = ({x} : Set (Fin n → ℝ)))
    (xSeq : ℕ → (Fin n → ℝ))
    (hnearMin :
      Filter.Tendsto (fun i : ℕ => f (xSeq i)) Filter.atTop (nhds (functionInfimumEReal f))) :
    Filter.Tendsto xSeq Filter.atTop (nhds x) := by
  -- First, the singleton minimum-set hypothesis rules out recession directions.
  have hnoRecession :
      HasNoRecessionDirections f :=
    helperForCorollary_6_27_2_hasNoRecessionDirections_of_singleton_minimumSet
      (f := f) hclosed hproper x hmin
  -- Then Corollary 6.27.1 gives boundedness of the sequence and forces every cluster point
  -- to lie in the minimum set.
  rcases
      nearMinimizingSequence_bounded_and_clusterPoints_mem_minimumSet_of_noRecessionDirections
        (f := f) hclosed hproper hnoRecession xSeq hnearMin with
    ⟨hBounded, hclusterInMin⟩
  have hUniqueCluster :
      ∀ y : Fin n → ℝ, MapClusterPt y Filter.atTop xSeq → y = x :=
    helperForCorollary_6_27_2_unique_clusterPoint
      (f := f) (x := x) hmin xSeq hclusterInMin
  -- Finally, boundedness puts the sequence in a compact closed ball, and uniqueness of cluster
  -- points upgrades compactness to actual convergence.
  rcases helperForCorollary_6_27_2_closedBall_eventually_contains_sequence
      (xSeq := xSeq) hBounded with ⟨R, _hRpos, hEventuallyBall⟩
  refine
    (isCompact_closedBall (0 : Fin n → ℝ) R).tendsto_nhds_of_unique_mapClusterPt
      hEventuallyBall ?_
  intro y _hyBall hyCluster
  exact hUniqueCluster y hyCluster

/-- A function has linewise infimum attainment when every affine line, written as
`{x + t • y | t : ℝ}` with `y ≠ 0`, contains a point where the restricted function attains its
infimum along that line. -/
def HasLinewiseInfimumAttainment {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x y : Fin n → ℝ, y ≠ 0 →
    ∃ t : ℝ, f (x + t • y) = ⨅ s : ℝ, f (x + s • y)

/-- Helper for Theorem 6.27.3: a point of `Fin 1 → ℝ` is determined by its unique scalar
coordinate. -/
lemma helperForTheorem_6_27_3_eq_scalarPoint (u : Fin 1 → ℝ) :
    scalarPoint (u 0) = u := by
  -- In dimension one, equality follows by checking the only coordinate.
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  simp [scalarPoint, hi]

/-- Helper for Theorem 6.27.3: the infimum of the scalarized line restriction over `Fin 1 → ℝ`
is the same as the usual infimum over real parameters. -/
lemma helperForTheorem_6_27_3_lineInfimum_eq_scalarRestrictionInfimum {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) :
    (⨅ u : Fin 1 → ℝ, f (x + (u 0) • y)) = ⨅ s : ℝ, f (x + s • y) := by
  -- Compare the two infima through the scalar embedding `scalarPoint : ℝ → Fin 1 → ℝ`.
  apply le_antisymm
  · refine le_iInf ?_
    intro s
    exact iInf_le (fun u : Fin 1 → ℝ => f (x + (u 0) • y)) (scalarPoint s)
  · refine le_iInf ?_
    intro u
    exact iInf_le (fun s : ℝ => f (x + s • y)) (u 0)

/-- Helper for Theorem 6.27.3: linewise attainment written with real parameters is equivalent to
attainment for the corresponding scalar restriction on `Fin 1 → ℝ`. -/
lemma helperForTheorem_6_27_3_scalarRestriction_attainment_iff {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) :
    (∃ t : ℝ, f (x + t • y) = ⨅ s : ℝ, f (x + s • y)) ↔
      ∃ uBar : Fin 1 → ℝ,
        f (x + (uBar 0) • y) = ⨅ u : Fin 1 → ℝ, f (x + (u 0) • y) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨scalarPoint t, ?_⟩
    -- Rewrite the `Fin 1` infimum back to the textbook scalar infimum on the line.
    calc
      f (x + ((scalarPoint t) 0) • y) = f (x + t • y) := by simp [scalarPoint]
      _ = ⨅ s : ℝ, f (x + s • y) := ht
      _ = ⨅ u : Fin 1 → ℝ, f (x + (u 0) • y) := by
        symm
        exact
          helperForTheorem_6_27_3_lineInfimum_eq_scalarRestrictionInfimum
            (f := f) x y
  · rintro ⟨uBar, huBar⟩
    refine ⟨uBar 0, ?_⟩
    -- Collapse the `Fin 1` witness to its scalar coordinate.
    calc
      f (x + (uBar 0) • y) = ⨅ u : Fin 1 → ℝ, f (x + (u 0) • y) := huBar
      _ = ⨅ s : ℝ, f (x + s • y) := by
        exact
          helperForTheorem_6_27_3_lineInfimum_eq_scalarRestrictionInfimum
            (f := f) x y

/-- Helper for Theorem 6.27.3: a strict decreasing-ray estimate along one affine line prevents the
corresponding scalar restriction from attaining its infimum. -/
lemma helperForTheorem_6_27_3_strictRay_produces_nonattaining_scalarLine {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x0 y0 : Fin n → ℝ)
    (hx0 : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (ε : ℝ) (hε : 0 < ε)
    (hRay :
      ∀ lam : ℝ, 0 ≤ lam →
        ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
          f (x + lam • y0) ≤ f x - ((lam * ε : ℝ) : EReal)) :
    ¬ ∃ uBar : Fin 1 → ℝ,
      f (x0 + (uBar 0) • y0) = ⨅ u : Fin 1 → ℝ, f (x0 + (u 0) • y0) := by
  rintro ⟨uBar, huBar⟩
  have hx0_top : f x0 < (⊤ : EReal) := by
    simpa [effectiveDomain_eq] using hx0
  have hmin_le_x0 :
      f (x0 + (uBar 0) • y0) ≤ f x0 := by
    -- Compare the alleged minimizer with the original anchor point `x0` on the same line.
    calc
      f (x0 + (uBar 0) • y0) = ⨅ u : Fin 1 → ℝ, f (x0 + (u 0) • y0) := huBar
      _ ≤ f (x0 + ((scalarPoint 0) 0) • y0) := by
        exact iInf_le (fun u : Fin 1 → ℝ => f (x0 + (u 0) • y0)) (scalarPoint 0)
      _ = f x0 := by simp [scalarPoint]
  have huDom :
      x0 + (uBar 0) • y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    have hu_top : f (x0 + (uBar 0) • y0) < (⊤ : EReal) := lt_of_le_of_lt hmin_le_x0 hx0_top
    simpa [effectiveDomain_eq] using hu_top
  have hnext_le :
      f (x0 + ((uBar 0 + 1) : ℝ) • y0) ≤
        f (x0 + (uBar 0) • y0) - ((1 * ε : ℝ) : EReal) := by
    -- Shift the strict-ray estimate to start at the minimizing point itself.
    simpa [one_smul, one_mul, add_smul, add_assoc, add_left_comm, add_comm] using
      hRay 1 (by norm_num) (x0 + (uBar 0) • y0) huDom
  have hmin_le_next :
      f (x0 + (uBar 0) • y0) ≤ f (x0 + ((uBar 0 + 1) : ℝ) • y0) := by
    -- Since `uBar` realizes the infimum, it cannot exceed the value at the shifted parameter.
    calc
      f (x0 + (uBar 0) • y0) = ⨅ u : Fin 1 → ℝ, f (x0 + (u 0) • y0) := huBar
      _ ≤ f (x0 + ((scalarPoint (uBar 0 + 1)) 0) • y0) := by
        exact
          iInf_le (fun u : Fin 1 → ℝ => f (x0 + (u 0) • y0))
            (scalarPoint (uBar 0 + 1))
      _ = f (x0 + ((uBar 0 + 1) : ℝ) • y0) := by simp [scalarPoint]
  have hu_top : f (x0 + (uBar 0) • y0) ≠ (⊤ : EReal) :=
    lt_top_iff_ne_top.mp (by
      simpa [effectiveDomain_eq] using huDom)
  have hu_bot : f (x0 + (uBar 0) • y0) ≠ (⊥ : EReal) :=
    hproper.2.2 (x0 + (uBar 0) • y0) (by simp)
  have hdrop_lt :
      f (x0 + (uBar 0) • y0) - ((1 * ε : ℝ) : EReal) <
        f (x0 + (uBar 0) • y0) := by
    -- Subtracting a positive real from a finite extended-real value is strictly decreasing.
    have hvalue_coe :
        ((((f (x0 + (uBar 0) • y0)).toReal : ℝ) : EReal)) =
          f (x0 + (uBar 0) • y0) := by
      simpa using EReal.coe_toReal (x := f (x0 + (uBar 0) • y0)) hu_top hu_bot
    have hlt_real :
        (f (x0 + (uBar 0) • y0)).toReal - (1 * ε : ℝ) <
          (f (x0 + (uBar 0) • y0)).toReal := by
      linarith
    have hlt_coe :
        ((((f (x0 + (uBar 0) • y0)).toReal - (1 * ε : ℝ) : ℝ) : EReal)) <
          ((((f (x0 + (uBar 0) • y0)).toReal : ℝ) : EReal)) := by
      exact EReal.coe_lt_coe_iff.2 hlt_real
    simpa [hvalue_coe, sub_eq_add_neg, one_mul] using hlt_coe
  exact (not_le_of_gt hdrop_lt) (le_trans hmin_le_next hnext_le)

/-- Helper for Theorem 6.27.3: linewise infimum attainment rules out the strict decreasing-ray
alternative from Theorem 6.27.1(g), so `0` must lie in the closure of `dom f*`. -/
lemma helperForTheorem_6_27_3_linewiseAttainment_rules_out_partG_badRay {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hline : HasLinewiseInfimumAttainment f) :
    (0 : Fin n → ℝ) ∈
      closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
  rcases closedProperConvexFunction_minimum_characterizations f hclosed hproper with
    ⟨_hA, _hB, _hC, _hD, _hE, _hF, hG, _hH, _hI⟩
  by_contra hNotClosure
  rcases hG.2.1 hNotClosure with ⟨y0, hy0, ε, hε, hRay⟩
  obtain ⟨x0, hx0⟩ :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (Set.univ : Set (Fin n → ℝ)) f).1 hproper.2.1
  have hbadLine :
      ¬ ∃ uBar : Fin 1 → ℝ,
        f (x0 + (uBar 0) • y0) = ⨅ u : Fin 1 → ℝ, f (x0 + (u 0) • y0) :=
    helperForTheorem_6_27_3_strictRay_produces_nonattaining_scalarLine
      (f := f) hproper x0 y0 hx0 ε hε hRay
  have hlineScalar :
      ∃ uBar : Fin 1 → ℝ,
        f (x0 + (uBar 0) • y0) = ⨅ u : Fin 1 → ℝ, f (x0 + (u 0) • y0) := by
    -- Convert the real-parameter linewise witness into the scalarized `Fin 1` form.
    exact
      (helperForTheorem_6_27_3_scalarRestriction_attainment_iff
        (f := f) x0 y0).1 (hline x0 y0 hy0)
  exact hbadLine hlineScalar

/-- Helper for Theorem 6.27.3: if linewise attainment holds but the global infimum is not
attained, then the origin is a boundary obstruction for `dom f*` and the minimum set is empty. -/
lemma helperForTheorem_6_27_3_boundary_obstruction_data_of_unattained_global_infimum {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hline : HasLinewiseInfimumAttainment f)
    (hnoMin : ¬ ∃ xBar : Fin n → ℝ, f xBar = functionInfimumEReal f) :
    (0 : Fin n → ℝ) ∈
        closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∧
      (0 : Fin n → ℝ) ∉
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∧
      ¬ (minimumSetEReal f).Nonempty := by
  rcases closedProperConvexFunction_minimum_characterizations f hclosed hproper with
    ⟨_hA, hB, _hC, _hD, _hE, _hF, _hG, _hH, _hI⟩
  have hNoMinSet : ¬ (minimumSetEReal f).Nonempty := by
    -- Any point of the minimum set would immediately contradict the assumed global nonattainment.
    intro hMin
    rcases hMin with ⟨xBar, hxBar⟩
    exact hnoMin ⟨xBar, hxBar⟩
  have hClosure :
      (0 : Fin n → ℝ) ∈
        closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) :=
    helperForTheorem_6_27_3_linewiseAttainment_rules_out_partG_badRay
      (f := f) hclosed hproper hline
  have hNotRelativeInterior :
      (0 : Fin n → ℝ) ∉
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
    -- Relative interior at the conjugate origin would create a subgradient there, hence a minimizer.
    intro hri
    have hSubNonempty :
        (euclideanSubdifferentialAt (fenchelConjugate n f) 0).Nonempty :=
      hB.2.2.1 hri
    have hMinNonempty : (minimumSetEReal f).Nonempty := (hB.2.1).2 hSubNonempty
    exact hNoMinSet hMinNonempty
  exact ⟨hClosure, hNotRelativeInterior, hNoMinSet⟩

/-- Helper for Theorem 6.27.3: in the bounded-below unattained case, part (c) of Theorem 6.27.1
already produces a `-∞` directional derivative of `f*` at the origin. -/
lemma helperForTheorem_6_27_3_partC_witness_of_lowerBound_and_unattained_global_infimum {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hLower : HasRealLowerBound f)
    (hnoMin : ¬ ∃ xBar : Fin n → ℝ, f xBar = functionInfimumEReal f) :
    ∃ y : Fin n → ℝ, upperDirectionalDerivativeAt (fenchelConjugate n f) 0 y = (⊥ : EReal) := by
  rcases closedProperConvexFunction_minimum_characterizations f hclosed hproper with
    ⟨_hA, _hB, hC, _hD, _hE, _hF, _hG, _hH, _hI⟩
  have hNoMinSet : ¬ (minimumSetEReal f).Nonempty := by
    -- Rewrite the textbook nonattainment statement in minimum-set form.
    intro hMin
    rcases hMin with ⟨xBar, hxBar⟩
    exact hnoMin ⟨xBar, hxBar⟩
  have hInf_ne_bot : functionInfimumEReal f ≠ (⊥ : EReal) :=
    (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot f).1 hLower
  have hInf_ne_top : functionInfimumEReal f ≠ (⊤ : EReal) := by
    -- Properness supplies one finite value, so the global infimum cannot be `+∞`.
    rcases hproper.2.1 with ⟨⟨x, μ⟩, hxμ⟩
    have hInf_le : functionInfimumEReal f ≤ f x := by
      simpa [functionInfimumEReal] using (iInf_le (fun y => f y) x)
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hInf_le (lt_of_le_of_lt hxμ.2 (by simp)))
  have hPartC :
      IsFiniteEReal (fenchelConjugate n f 0) ∧
        ∃ y : Fin n → ℝ, upperDirectionalDerivativeAt (fenchelConjugate n f) 0 y = (⊥ : EReal) :=
    hC.1 ⟨⟨hInf_ne_top, hInf_ne_bot⟩, hNoMinSet⟩
  -- Keep only the directional-derivative witness; the finite-value side is bookkeeping for part (c).
  exact hPartC.2

/-- Helper for Theorem 6.27.3: if the minimum set is empty, then the conjugate has no
subgradient at the origin. -/
lemma helperForTheorem_6_27_3_conjugate_subdifferential_empty_of_noMinSet {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hNoMinSet : ¬ (minimumSetEReal f).Nonempty) :
    ¬ Set.Nonempty (subdifferentialAt (fenchelConjugate n f) 0) := by
  have hMinEq :
      minimumSetEReal f = euclideanSubdifferentialAt (fenchelConjugate n f) 0 :=
    helperForTheorem_6_27_1_minimumSet_eq_euclideanSubdifferentialAt_conjugate_zero
      f hclosed hproper
  have hNonemptyEq :
      Set.Nonempty (subdifferentialAt (fenchelConjugate n f) 0) ↔
        (euclideanSubdifferentialAt (fenchelConjugate n f) 0).Nonempty := by
    constructor
    · rintro ⟨xStar, hxStar⟩
      -- Move from the dual subgradient to its Euclidean coordinate representative.
      exact ⟨(dotProductEquiv ℝ (Fin n)).symm xStar, by
        simpa [euclideanSubdifferentialAt] using hxStar⟩
    · rintro ⟨x, hx⟩
      -- Move back by evaluating the Euclidean vector as a dot-product functional.
      exact ⟨dotProductEquiv ℝ (Fin n) x, by
        simpa [euclideanSubdifferentialAt] using hx⟩
  intro hSubNonempty
  have hEuclideanNonempty :
      (euclideanSubdifferentialAt (fenchelConjugate n f) 0).Nonempty :=
    hNonemptyEq.1 hSubNonempty
  have hMinNonempty : (minimumSetEReal f).Nonempty := by
    -- The minimum-set/subdifferential identification now turns that fiber point into a minimizer.
    simpa [hMinEq] using hEuclideanNonempty
  exact hNoMinSet hMinNonempty

/-- Helper for Theorem 6.27.3: once `f` is bounded below but has empty minimum set, Theorem 23.3
upgrades the part-(c) obstruction to a bilateral directional-derivative witness for `f*` at the
origin. -/
lemma helperForTheorem_6_27_3_bilateral_conjugate_directional_witness_of_lowerBound_and_noMinSet
    {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hLower : HasRealLowerBound f)
    (hNoMinSet : ¬ (minimumSetEReal f).Nonempty) :
    ∃ y : Fin n → ℝ,
      upperDirectionalDerivativeAt (fenchelConjugate n f) 0 y = (⊥ : EReal) ∧
        upperDirectionalDerivativeAt (fenchelConjugate n f) 0 (-y) = (⊤ : EReal) := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hA := helperForTheorem_6_27_1_conjugateAtZero_eq_neg_functionInfimumEReal f
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hconvStar : ConvexFunction fStar := by
    simpa [fStar, ConvexFunction] using hproperStar.1
  have h0Dom :
      (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar :=
    hA.2.1 hLower
  have h0Finite : fStar 0 ≠ (⊤ : EReal) ∧ fStar 0 ≠ (⊥ : EReal) := by
    constructor
    · -- Lower boundedness puts `0` in `dom f*`, so the conjugate is not `+∞` there.
      rw [effectiveDomain_eq] at h0Dom
      exact lt_top_iff_ne_top.mp h0Dom.2
    · -- Properness of the conjugate rules out `-∞` at every point.
      exact hproperStar.2.2 0 (by simp)
  have hSubEmpty : ¬ Set.Nonempty (subdifferentialAt fStar 0) :=
    helperForTheorem_6_27_3_conjugate_subdifferential_empty_of_noMinSet
      (f := f) hclosed hproper hNoMinSet
  rcases
      (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
        fStar hconvStar 0 h0Finite).2 hSubEmpty with
    ⟨⟨y, hyBot, hyOppTop⟩, _hRelativeInteriorFamily⟩
  -- Keep only the explicit bilateral witness; the relative-interior transport clause is not yet
  -- used in this part file.
  exact ⟨y, hyBot, hyOppTop⟩

/-- Helper for Theorem 6.27.3: boundary failure of relative interior at the conjugate origin
produces a nonzero recession direction that is not a direction of constancy. -/
lemma helperForTheorem_6_27_3_nonconstant_recession_direction_of_boundary_obstruction {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hClosure :
      (0 : Fin n → ℝ) ∈
        closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)))
    (hNotRelativeInterior :
      (0 : Fin n → ℝ) ∉
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) :
    ∃ y : Fin n → ℝ, y ≠ 0 ∧ IsRecessionDirection f y ∧ ¬ IsDirectionOfConstancy f y := by
  rcases closedProperConvexFunction_minimum_characterizations f hclosed hproper with
    ⟨_hA, hB, _hC, _hD, _hE, _hF, hG, _hH, _hI⟩
  have hNotEveryConst : ¬ EveryRecessionDirectionIsConstant f := by
    -- The part-(b) equivalence turns the failure of relative interior into failure of
    -- constancy for some recession direction.
    intro hEveryConst
    exact hNotRelativeInterior ((hB.2.2.2).2 hEveryConst)
  have hExists :
      ∃ y : Fin n → ℝ, IsRecessionDirection f y ∧ ¬ IsDirectionOfConstancy f y := by
    -- Otherwise every recession direction would be constant, contradicting the previous step.
    by_contra hNoWitness
    apply hNotEveryConst
    intro y hyRec
    by_contra hyNotConst
    exact hNoWitness ⟨y, hyRec, hyNotConst⟩
  rcases hExists with ⟨y, hyRec, hyNotConst⟩
  have hNonneg : ∀ z : Fin n → ℝ, (0 : EReal) ≤ recessionFunction f z := hG.1.1 hClosure
  have hyZero : recessionFunction f y = 0 := le_antisymm hyRec (hNonneg y)
  have hy_ne : y ≠ 0 := by
    -- Under the closure hypothesis, the zero direction is automatically a direction of constancy.
    intro hyEq
    apply hyNotConst
    constructor
    · exact hyZero
    · simpa [hyEq] using hyZero
  exact ⟨y, hy_ne, hyRec, hyNotConst⟩

/-- Helper for Theorem 6.27.3: the same boundary obstruction can be normalized to an asymmetric
recession witness with vanishing recession in one direction and strictly positive recession in the
opposite direction. -/
lemma helperForTheorem_6_27_3_asymmetric_recession_witness_of_boundary_obstruction {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hClosure :
      (0 : Fin n → ℝ) ∈
        closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)))
    (hNotRelativeInterior :
      (0 : Fin n → ℝ) ∉
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) :
    ∃ y : Fin n → ℝ, y ≠ 0 ∧
      recessionFunction f y = 0 ∧ (0 : EReal) < recessionFunction f (-y) := by
  rcases closedProperConvexFunction_minimum_characterizations f hclosed hproper with
    ⟨_hA, _hB, _hC, _hD, _hE, _hF, hG, _hH, _hI⟩
  obtain ⟨y, hy_ne, hyRec, hyNotConst⟩ :=
    helperForTheorem_6_27_3_nonconstant_recession_direction_of_boundary_obstruction
      (f := f) hclosed hproper hClosure hNotRelativeInterior
  have hNonneg : ∀ z : Fin n → ℝ, (0 : EReal) ≤ recessionFunction f z := hG.1.1 hClosure
  have hyZero : recessionFunction f y = 0 := le_antisymm hyRec (hNonneg y)
  have hneg_ne_zero : recessionFunction f (-y) ≠ 0 := by
    -- Nonconstancy means the opposite recession value cannot also vanish.
    intro hnegZero
    exact hyNotConst ⟨hyZero, hnegZero⟩
  have hneg_pos : (0 : EReal) < recessionFunction f (-y) := by
    -- The closure criterion gives nonnegativity in every direction, so strict positivity is
    -- exactly the failure of the opposite recession value to be zero.
    exact lt_of_le_of_ne (hNonneg (-y)) (Ne.symm hneg_ne_zero)
  exact ⟨y, hy_ne, hyZero, hneg_pos⟩

/-- Helper for Theorem 6.27.3: vanishing recession in direction `y` forces every forward
translate along `y` to be nonincreasing on the effective domain. -/
lemma helperForTheorem_6_27_3_zero_recession_gives_ray_nonincrease {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {y : Fin n → ℝ} (hyZero : recessionFunction f y = 0) :
    ∀ lam : ℝ, 0 ≤ lam →
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f, f (x + lam • y) ≤ f x := by
  let domFstar : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hCne : domFstar.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
  have hCconv : Convex ℝ domFstar := by
    have hconvStar : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    have hconvOn :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      simpa [ConvexFunction] using hconvStar
    simpa [domFstar] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ)))
        (f := fenchelConjugate n f) (hf := hconvOn))
  have hsupp_eq :
      supportFunctionEReal domFstar = recessionFunction f := by
    simpa [domFstar] using
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
        (n := n) (f := f) hclosed hproper
  have hposHom : PositivelyHomogeneous (supportFunctionEReal domFstar) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom
      (n := n) (C := domFstar) hCne hCconv).2.2
  intro lam hlam x hx
  by_cases hlam_zero : lam = 0
  · -- The zero step leaves the anchor point unchanged.
    simp [hlam_zero]
  · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_zero)
    have hscaled :
        recessionFunction f (lam • y) ≤ (0 : EReal) := by
      calc
        recessionFunction f (lam • y) = supportFunctionEReal domFstar (lam • y) := by
          exact (congrArg (fun g => g (lam • y)) hsupp_eq).symm
        _ = ((lam : ℝ) : EReal) * supportFunctionEReal domFstar y := by
          simpa using hposHom y lam hlam_pos
        _ = ((lam : ℝ) : EReal) * recessionFunction f y := by
          simp [congrArg (fun g => g y) hsupp_eq]
        _ = ((lam : ℝ) : EReal) * (0 : EReal) := by simp [hyZero]
        _ = (0 : EReal) := by
          have hlamE : (0 : EReal) ≤ ((lam : ℝ) : EReal) := by
            exact_mod_cast hlam
          simp
        _ ≤ (0 : EReal) := le_rfl
    have hdiff :
        f (x + lam • y) - f x ≤ recessionFunction f (lam • y) := by
      -- The recession function is the supremum of these translated differences.
      exact le_sSup ⟨x, hx, rfl⟩
    have hx_top_lt : f x < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx
    have hx_top : f x ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx_top_lt
    have hx_bot : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
    have hle_add :
        f (x + lam • y) ≤ recessionFunction f (lam • y) + f x :=
      (EReal.sub_le_iff_le_add
        (a := f (x + lam • y)) (b := f x) (c := recessionFunction f (lam • y))
        (Or.inl hx_bot) (Or.inl hx_top)).1 hdiff
    calc
      f (x + lam • y) ≤ recessionFunction f (lam • y) + f x := hle_add
      _ ≤ (0 : EReal) + f x := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right hscaled (f x)
      _ = f x := by simp


end Section27
end Chap06
