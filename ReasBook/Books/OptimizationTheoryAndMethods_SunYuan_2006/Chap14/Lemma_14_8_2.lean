/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.OpenPos
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_2

noncomputable section

open Filter

section Chapter14Lemma1482

variable {n : ℕ}

open scoped GeneralizedJacobian

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Operator" => Point →L[ℝ] Point

-- Source/core/bridge triage:
-- * source-facing: Lemma 14.8.2, a neighborhood inverse-bound statement for `∂F`
-- * core/canonical: `generalizedJacobian F x : Set Operator`
--   from `Chapter14.Definition_14_8_extra_2`
-- * bridge/view: the deleted matrix-coordinate presentation, which carried no extra mathematics

/-- Helper for Chapter14 Lemma 14.8.2: a closed-ball Lipschitz witness centered at `x`
restricts to a smaller closed-ball witness centered at any point `y` in the half-radius ball
around `x`. -/
lemma locallyLipschitzAt_of_mem_ball_of_closedBallLipschitz
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2)) :
    LocallyLipschitzAt F y := by
  -- Shrink the original closed ball to a centered half-radius closed ball around `y`.
  refine locallyLipschitzAt_of_closedBall (K := K) ?_
  refine ⟨ε / 2, by positivity, ?_⟩
  refine hK.mono ?_
  intro z hz
  have hy_le : dist y x ≤ ε / 2 := le_of_lt (Metric.mem_ball.1 hy)
  have hz_le : dist z y ≤ ε / 2 := Metric.mem_closedBall.1 hz
  -- The triangle inequality keeps every `z` in the original Lipschitz closed ball.
  refine Metric.mem_closedBall.2 ?_
  calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring

/-- Helper for Chapter14 Lemma 14.8.2: if `y ∈ Metric.ball x ε`, then the corresponding closed
ball `Metric.closedBall x ε` is a neighborhood of `y`. -/
lemma closedBall_mem_nhds_of_mem_ball
    {x y : Point} {ε : ℝ}
    (hy : y ∈ Metric.ball x ε) :
    Metric.closedBall x ε ∈ nhds y := by
  rcases Metric.mem_ball.1 hy with hy_lt
  have hrad : 0 < ε - dist y x := by linarith
  refine Filter.mem_of_superset (Metric.ball_mem_nhds y hrad) ?_
  intro z hz
  have hz_lt : dist z y < ε - dist y x := Metric.mem_ball.1 hz
  refine Metric.mem_closedBall.2 ?_
  exact le_of_lt <| calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ < (ε - dist y x) + dist y x := by linarith
    _ = ε := by ring

/-- Helper for Chapter14 Lemma 14.8.2: every generalized-Jacobian element at a point `y` in the
half-radius ball around `x` lies in the common operator closed ball determined by the original
closed-ball Lipschitz constant. -/
lemma mem_closedBall_generalizedJacobian_of_closedBallLipschitzNear
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2))
    {V : Operator}
    (hV : V ∈ (∂ F) y) :
    V ∈ Metric.closedBall (0 : Operator) (K : ℝ) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hKy : LipschitzOnWith K F (Metric.closedBall y (ε / 2)) := by
    -- Recenter the original Lipschitz estimate at `y` by the half-radius inclusion.
    refine hK.mono ?_
    intro z hz
    have hy_le : dist y x ≤ ε / 2 := le_of_lt (Metric.mem_ball.1 hy)
    have hz_le : dist z y ≤ ε / 2 := Metric.mem_closedBall.1 hz
    refine Metric.mem_closedBall.2 ?_
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := by ring
  rw [mem_generalizedJacobian_iff] at hV
  have hsubset :
      {A : Operator | ∃ xs : ℕ → Point,
          Filter.Tendsto xs Filter.atTop (nhds y) ∧
          (∀ i : ℕ, DifferentiableAt ℝ F (xs i)) ∧
          Filter.Tendsto (fun i : ℕ ↦ fderiv ℝ F (xs i)) Filter.atTop (nhds A)} ⊆
        Metric.closedBall (0 : Operator) (K : ℝ) := by
    intro A hA
    rcases hA with ⟨xs, hxs, hdiff, hlim⟩
    have hinside :
        ∀ᶠ i in Filter.atTop, xs i ∈ Metric.ball y (ε / 2) :=
      hxs (Metric.ball_mem_nhds y hε2)
    have hderiv_mem :
        ∀ᶠ i in Filter.atTop, fderiv ℝ F (xs i) ∈ Metric.closedBall (0 : Operator) (K : ℝ) := by
      filter_upwards [hinside] with i hxi
      have hnhds :
          Metric.closedBall y (ε / 2) ∈ nhds (xs i) :=
        closedBall_mem_nhds_of_mem_ball (x := y) (y := xs i) (ε := ε / 2) hxi
      have hnorm : ‖fderiv ℝ F (xs i)‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn ℝ hnhds hKy
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    -- Pass the uniform derivative bound to the limiting operator.
    exact IsClosed.mem_of_tendsto Metric.isClosed_closedBall hlim hderiv_mem
  have hclosedBall_convex :
      Convex ℝ (Metric.closedBall (0 : Operator) (K : ℝ)) := by
    simpa [Metric.closedBall] using convex_closedBall (0 : Operator) (K : ℝ)
  -- Close the target through the convexity of the operator ball after unfolding `(∂ F) y`.
  exact (convexHull_min hsubset hclosedBall_convex) hV

/-- Helper for Chapter14 Lemma 14.8.2: the raw sequential generators whose convex hull defines
`(∂ F) x = ∂F(x)`. -/
def generalizedJacobianGeneratorSet
    (F : Point → Point) (x : Point) : Set Operator :=
  {A : Operator | ∃ xs : ℕ → Point,
      Filter.Tendsto xs Filter.atTop (nhds x) ∧
      (∀ i : ℕ, DifferentiableAt ℝ F (xs i)) ∧
      Filter.Tendsto (fun i : ℕ ↦ fderiv ℝ F (xs i)) Filter.atTop (nhds A)}

/-- Helper for Chapter14 Lemma 14.8.2: nearby derivative values taken at differentiability points
inside a closed ball around `x`. -/
def nearbyDerivativeValues
    (F : Point → Point) (x : Point) (r : ℝ) : Set Operator :=
  {A : Operator | ∃ z : Point,
      z ∈ Metric.closedBall x r ∧
      DifferentiableAt ℝ F z ∧
      fderiv ℝ F z = A}

/-- Helper for Chapter14 Lemma 14.8.2: unfolding `(∂ F) x` through the explicit raw generator
owner only changes notation. -/
lemma generalizedJacobian_eq_convexHull_generatorSet
    (F : Point → Point) (x : Point) :
    (∂ F) x = convexHull ℝ (generalizedJacobianGeneratorSet F x) := by
  rfl

/-- Helper for Chapter14 Lemma 14.8.2: every raw generator already belongs to the public
generalized Jacobian `(∂ F) x`. -/
lemma mem_generalizedJacobian_of_mem_generatorSet
    {F : Point → Point} {x : Point} {A : Operator}
    (hA : A ∈ generalizedJacobianGeneratorSet F x) :
    A ∈ (∂ F) x := by
  -- The raw generator set is the defining subset of the convex hull owner.
  rw [generalizedJacobian_eq_convexHull_generatorSet]
  exact subset_convexHull ℝ (s := generalizedJacobianGeneratorSet F x) hA

/-- Helper for Chapter14 Lemma 14.8.2: a raw generator belongs to all shrinking nearby-derivative
closures around its base point. -/
lemma mem_iInter_closure_nearbyDerivativeValues_of_mem_generalizedJacobianGeneratorSet
    (F : Point → Point) (x : Point)
    {A : Operator}
    (hA : A ∈ generalizedJacobianGeneratorSet F x) :
    A ∈ ⋂ n : ℕ, closure (nearbyDerivativeValues F x (1 / (n + 1 : ℝ))) := by
  rcases hA with ⟨xs, hxs, hdiff, hlim⟩
  rw [Set.mem_iInter]
  intro n
  rw [mem_closure_iff_nhds]
  intro s hs
  have hs_event :
      ∀ᶠ i in Filter.atTop, fderiv ℝ F (xs i) ∈ s :=
    hlim hs
  have hball_event :
      ∀ᶠ i in Filter.atTop, xs i ∈ Metric.closedBall x (1 / (n + 1 : ℝ)) := by
    have hrad : 0 < (1 / (n + 1 : ℝ)) := by positivity
    exact hxs (Metric.closedBall_mem_nhds x hrad)
  -- Intersect the derivative limit with the shrinking closed-ball witness.
  have h_event :
      ∀ᶠ i in Filter.atTop,
        fderiv ℝ F (xs i) ∈ s ∩ nearbyDerivativeValues F x (1 / (n + 1 : ℝ)) := by
    filter_upwards [hs_event, hball_event] with i hsi hxi
    exact ⟨hsi, xs i, hxi, hdiff i, rfl⟩
  rcases Filter.eventually_atTop.1 h_event with ⟨N, hN⟩
  exact ⟨fderiv ℝ F (xs N), hN N le_rfl⟩

/-- Helper for Chapter14 Lemma 14.8.2: membership in all shrinking nearby-derivative closures
reconstructs a raw generalized-Jacobian generator. -/
lemma mem_generalizedJacobianGeneratorSet_of_mem_iInter_closure_nearbyDerivativeValues
    (F : Point → Point) (x : Point)
    {A : Operator}
    (hA : A ∈ ⋂ n : ℕ, closure (nearbyDerivativeValues F x (1 / (n + 1 : ℝ)))) :
    A ∈ generalizedJacobianGeneratorSet F x := by
  have hchoose :
      ∀ n : ℕ, ∃ z : Point,
        z ∈ Metric.closedBall x (1 / (n + 1 : ℝ)) ∧
        DifferentiableAt ℝ F z ∧
        fderiv ℝ F z ∈ Metric.ball A (1 / (n + 1 : ℝ)) := by
    intro n
    have hAn :
        A ∈ closure (nearbyDerivativeValues F x (1 / (n + 1 : ℝ))) :=
      Set.mem_iInter.mp hA n
    have hrad : 0 < (1 / (n + 1 : ℝ)) := by positivity
    have hball : Metric.ball A (1 / (n + 1 : ℝ)) ∈ nhds A :=
      Metric.ball_mem_nhds A hrad
    rcases (mem_closure_iff_nhds.1 hAn) (Metric.ball A (1 / (n + 1 : ℝ))) hball with
      ⟨B, hBball, hBnearby⟩
    rcases hBnearby with ⟨z, hz, hdiff, rfl⟩
    exact ⟨z, hz, hdiff, hBball⟩
  choose zs hzs_mem hzs_diff hzs_close using hchoose
  refine ⟨zs, ?_, hzs_diff, ?_⟩
  · -- The shrinking closed-ball radii force the sampled differentiability points back to `x`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases (Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))) ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hdist :
        dist (zs n) x ≤ 1 / (n + 1 : ℝ) :=
      Metric.mem_closedBall.1 (hzs_mem n)
    have hN' : |(1 / (n + 1 : ℝ))| < ε := by
      simpa [Real.dist_eq] using hN n hn
    have hradius :
        1 / (n + 1 : ℝ) < ε :=
      (abs_lt.mp hN').2
    exact lt_of_le_of_lt hdist hradius
  · -- The sampled Jacobians stay in shrinking metric balls around `A`, so they converge to `A`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases (Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))) ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hN' : |(1 / (n + 1 : ℝ))| < ε := by
      simpa [Real.dist_eq] using hN n hn
    have hradius :
        1 / (n + 1 : ℝ) < ε :=
      (abs_lt.mp hN').2
    exact lt_trans (Metric.mem_ball.1 (hzs_close n)) hradius

/-- Helper for Chapter14 Lemma 14.8.2: the raw generator set equals the intersection of the
shrinking nearby-derivative closures. -/
lemma generalizedJacobianGeneratorSet_eq_iInter_closure_nearbyDerivativeValues
    (F : Point → Point) (x : Point) :
    generalizedJacobianGeneratorSet F x =
      ⋂ n : ℕ, closure (nearbyDerivativeValues F x (1 / (n + 1 : ℝ))) := by
  ext A
  constructor
  · intro hA
    exact
      mem_iInter_closure_nearbyDerivativeValues_of_mem_generalizedJacobianGeneratorSet
        (F := F) (x := x) hA
  · intro hA
    exact
      mem_generalizedJacobianGeneratorSet_of_mem_iInter_closure_nearbyDerivativeValues
        (F := F) (x := x) hA

/-- Helper for Chapter14 Lemma 14.8.2: the raw generator set is closed. -/
lemma isClosed_generalizedJacobianGeneratorSet
    (F : Point → Point) (x : Point) :
    IsClosed (generalizedJacobianGeneratorSet F x) := by
  -- Rewrite the generator owner as a countable intersection of closed shells.
  rw [generalizedJacobianGeneratorSet_eq_iInter_closure_nearbyDerivativeValues (F := F) (x := x)]
  exact isClosed_iInter fun n => isClosed_closure

/-- Helper for Chapter14 Lemma 14.8.2: moving the base point by at most `R - r` transports a
nearby-derivative shell of radius `r` into the shell of radius `R`. -/
lemma nearbyDerivativeValues_subset_of_dist_add_le
    {F : Point → Point} {x y : Point} {r R : ℝ}
    (hxy : dist y x + r ≤ R) :
    nearbyDerivativeValues F y r ⊆ nearbyDerivativeValues F x R := by
  intro A hA
  rcases hA with ⟨z, hz, hdiff, rfl⟩
  refine ⟨z, ?_, hdiff, rfl⟩
  refine Metric.mem_closedBall.2 ?_
  calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ ≤ r + dist y x := by gcongr; exact Metric.mem_closedBall.1 hz
    _ = dist y x + r := by ring
    _ ≤ R := hxy

/-- Helper for Chapter14 Lemma 14.8.2: the reciprocal radius at index `2 * m + 1` is exactly one
half of the reciprocal radius at index `m`. -/
lemma reciprocal_doubleIndex_add_eq
    (m : ℕ) :
    (1 / ((2 * m + 1) + 1 : ℝ)) + (1 / ((2 * m + 1) + 1 : ℝ)) =
      1 / (m + 1 : ℝ) := by
  field_simp
  ring

/-- Helper for Chapter14 Lemma 14.8.2: every nearby raw generator inherits the common operator
closed-ball bound from the ambient closed-ball Lipschitz shell around `x`. -/
lemma mem_closedBall_generalizedJacobianGeneratorSet_of_closedBallLipschitzNear
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2))
    {A : Operator}
    (hA : A ∈ generalizedJacobianGeneratorSet F y) :
    A ∈ Metric.closedBall (0 : Operator) (K : ℝ) := by
  -- Promote the generator to the public generalized Jacobian and reuse the uniform bound.
  exact
    mem_closedBall_generalizedJacobian_of_closedBallLipschitzNear
      (F := F) (x := x) (ε := ε) (K := K) hε hK hy
      (mem_generalizedJacobian_of_mem_generatorSet hA)

/-- Helper for Chapter14 Lemma 14.8.2: the nearby raw generator set is compact because it is a
closed subset of the common operator closed ball. -/
lemma isCompact_generalizedJacobianGeneratorSet_of_closedBallLipschitzNear
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2)) :
    IsCompact (generalizedJacobianGeneratorSet F y) := by
  have hclosed :
      IsClosed (generalizedJacobianGeneratorSet F y) :=
    isClosed_generalizedJacobianGeneratorSet (F := F) (x := y)
  have hsubset :
      generalizedJacobianGeneratorSet F y ⊆ Metric.closedBall (0 : Operator) (K : ℝ) := by
    intro A hA
    exact
      mem_closedBall_generalizedJacobianGeneratorSet_of_closedBallLipschitzNear
        (F := F) (x := x) (ε := ε) (K := K) hε hK hy hA
  -- Compactness follows from the finite-dimensional operator closed ball.
  exact (isCompact_closedBall (x := (0 : Operator)) (r := (K : ℝ))).of_isClosed_subset
    hclosed hsubset

/-- Helper for Chapter14 Lemma 14.8.2: in the finite-dimensional operator space, the convex hull
of a compact set is compact. -/
lemma isCompact_convexHull_of_isCompact
    {s : Set Operator}
    (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  let d : ℕ := Module.finrank ℝ Operator + 1
  let representation : Fin (d + 1) → Set Operator := fun k =>
    (fun p : (Fin k.1 → Operator) × (Fin k.1 → ℝ) ↦ ∑ i, p.2 i • p.1 i) ''
      (({z : Fin k.1 → Operator | ∀ i, z i ∈ s}) ×ˢ stdSimplex ℝ (Fin k.1))
  have hrepresentation_compact : ∀ k : Fin (d + 1), IsCompact (representation k) := by
    intro k
    have hpoints :
        IsCompact {z : Fin k.1 → Operator | ∀ i, z i ∈ s} := by
      simpa using isCompact_pi_infinite fun _ : Fin k.1 => hs
    have hweights : IsCompact (stdSimplex ℝ (Fin k.1)) :=
      isCompact_stdSimplex ℝ (Fin k.1)
    have hproduct :
        IsCompact
          (({z : Fin k.1 → Operator | ∀ i, z i ∈ s}) ×ˢ
            stdSimplex ℝ (Fin k.1)) :=
      hpoints.prod hweights
    have hsum :
        Continuous
          (fun p : (Fin k.1 → Operator) × (Fin k.1 → ℝ) ↦
            ∑ i, p.2 i • p.1 i) := by
      -- The finite weighted-sum parametrization is continuous in both the points and weights.
      simpa using
        continuous_finsetSum Finset.univ fun i _ =>
          (((continuous_apply i).comp continuous_snd).smul
            ((continuous_apply i).comp continuous_fst))
    -- Package the Caratheodory coordinates as a compact parameter space and take its image.
    exact hproduct.image hsum
  have hsubset :
      convexHull ℝ s ⊆ ⋃ k : Fin (d + 1), representation k := by
    intro x hx
    rcases eq_pos_convex_span_of_mem_convexHull hx with
      ⟨ι, _, z, w, hz, hz_aff, hw_pos, hw_sum, hwx⟩
    have hcard :
        Fintype.card ι ≤ d := by
      exact le_trans hz_aff.card_le_finrank_succ (Nat.succ_le_succ (Submodule.finrank_le _))
    let k : Fin (d + 1) := ⟨Fintype.card ι, Nat.lt_succ_of_le hcard⟩
    let e : ι ≃ Fin k.1 := Fintype.equivFin ι
    let z' : Fin k.1 → Operator := fun i ↦ z (e.symm i)
    let w' : Fin k.1 → ℝ := fun i ↦ w (e.symm i)
    have hz' : ∀ i, z' i ∈ s := by
      intro i
      simpa [z'] using hz (Set.mem_range_self (e.symm i))
    have hw' : w' ∈ stdSimplex ℝ (Fin k.1) := by
      refine ⟨?_, ?_⟩
      · intro i
        exact le_of_lt (hw_pos (e.symm i))
      · have hsum_eq :
            ∑ i : Fin k.1, w' i = ∑ i : ι, w i :=
          Fintype.sum_equiv e.symm w' w fun i => rfl
        exact hsum_eq.trans hw_sum
    have hwx' : ∑ i : Fin k.1, w' i • z' i = x := by
      have hsum_eq :
            ∑ i : Fin k.1, w' i • z' i = ∑ i : ι, w i • z i :=
          Fintype.sum_equiv e.symm (fun i : Fin k.1 => w' i • z' i)
            (fun i : ι => w i • z i) fun i => rfl
      exact hsum_eq.trans hwx
    -- Reindex the Caratheodory coordinates onto a fixed finite type.
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    exact ⟨(z', w'), ⟨hz', hw'⟩, hwx'⟩
  have hsuperset :
      (⋃ k : Fin (d + 1), representation k) ⊆ convexHull ℝ s := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hxk⟩
    rcases hxk with ⟨p, hp, rfl⟩
    -- Any compact-parameter witness is already a convex combination of points of `s`.
    exact
      mem_convexHull_of_exists_fintype (w := p.2) (z := p.1)
        (fun i => hp.2.1 i) hp.2.2 (fun i => hp.1 i) rfl
  have hrepresentation :
      convexHull ℝ s = ⋃ k : Fin (d + 1), representation k :=
    Set.Subset.antisymm hsubset hsuperset
  -- The convex hull is a finite union of compact representation sets.
  rw [hrepresentation]
  exact isCompact_iUnion hrepresentation_compact

/-- Helper for Chapter14 Lemma 14.8.2: the public generalized Jacobian is compact whenever the raw
generator set is compact in the surrounding Lipschitz shell. -/
lemma isCompact_generalizedJacobian_of_closedBallLipschitzNear
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2)) :
    IsCompact ((∂ F) y) := by
  -- Rewrite the public owner through the compact raw generators, then take a compact convex hull.
  rw [generalizedJacobian_eq_convexHull_generatorSet]
  exact
    isCompact_convexHull_of_isCompact
      (isCompact_generalizedJacobianGeneratorSet_of_closedBallLipschitzNear
        (F := F) (x := x) (ε := ε) (K := K) hε hK hy)

/-- Helper for Chapter14 Lemma 14.8.2: nearby local Lipschitz regularity provides a raw
generalized-Jacobian generator at every point of the half-radius ball around `x`. -/
lemma generalizedJacobianGeneratorSetNonempty_of_closedBallLipschitzNear
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2)) :
    (generalizedJacobianGeneratorSet F y).Nonempty := by
  let h_local_y :=
    locallyLipschitzAt_of_mem_ball_of_closedBallLipschitz
      (F := F) (x := x) (ε := ε) (K := K) hε hK hy
  rcases locallyLipschitzAt_iff.mp h_local_y with ⟨δ, hδ, K', hK'⟩
  have h_dense :
      Dense {z : Point | z ∈ Metric.closedBall y δ →
        DifferentiableWithinAt ℝ F (Metric.closedBall y δ) z} := by
    exact MeasureTheory.Measure.dense_of_ae
      (μ := MeasureTheory.volume)
      ((LipschitzOnWith.ae_differentiableWithinAt_of_mem (μ := MeasureTheory.volume) hK'))
  have hpick :
      ∀ n : ℕ, ∃ z : Point,
        z ∈ Metric.ball y (min (δ / 2) (1 / (n + 1 : ℝ))) ∧
        z ∈ Metric.closedBall y δ ∧
        DifferentiableAt ℝ F z := by
    intro n
    have hrad : 0 < min (δ / 2) (1 / (n + 1 : ℝ)) := by
      positivity
    rcases h_dense.inter_open_nonempty
        (Metric.ball y (min (δ / 2) (1 / (n + 1 : ℝ))))
        (Metric.isOpen_ball)
        ⟨y, Metric.mem_ball_self hrad⟩ with ⟨z, hzball, hzprop⟩
    have hz_closed : z ∈ Metric.closedBall y δ := by
      refine Metric.mem_closedBall.2 <| le_of_lt ?_
      calc
        dist z y < min (δ / 2) (1 / (n + 1 : ℝ)) := Metric.mem_ball.1 hzball
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have hz_diffWithin :
        DifferentiableWithinAt ℝ F (Metric.closedBall y δ) z :=
      hzprop hz_closed
    have hz_nhds :
        Metric.closedBall y δ ∈ nhds z :=
      closedBall_mem_nhds_of_mem_ball
        (x := y) (y := z) (ε := δ) (by
          refine Metric.mem_ball.2 ?_
          exact lt_trans (Metric.mem_ball.1 hzball) (by
            have : min (δ / 2) (1 / (n + 1 : ℝ)) ≤ δ / 2 := min_le_left _ _
            linarith))
    have hz_diff : DifferentiableAt ℝ F z :=
      hz_diffWithin.differentiableAt hz_nhds
    exact ⟨z, hzball, hz_closed, hz_diff⟩
  choose zs hzs_ball hzs_closed hzs_diff using hpick
  have hzs_tendsto : Tendsto zs atTop (nhds y) := by
    -- The shrinking ball radii force the chosen differentiability points back to `y`.
    rw [Metric.tendsto_atTop]
    intro ρ hρ
    rcases (Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))) ρ hρ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hN' : |(1 / (n + 1 : ℝ))| < ρ := by
      simpa [Real.dist_eq] using hN n hn
    have hone : 1 / (n + 1 : ℝ) < ρ :=
      (abs_lt.mp hN').2
    have hdist :
        dist (zs n) y < 1 / (n + 1 : ℝ) :=
      lt_of_lt_of_le (Metric.mem_ball.1 (hzs_ball n)) (min_le_right _ _)
    exact lt_trans hdist hone
  have hderiv_mem :
      ∀ n, fderiv ℝ F (zs n) ∈ Metric.closedBall (0 : Operator) (K' : ℝ) := by
    intro n
    have hnhds :
        Metric.closedBall y δ ∈ nhds (zs n) :=
      closedBall_mem_nhds_of_mem_ball
        (x := y) (y := zs n) (ε := δ) (by
          refine Metric.mem_ball.2 ?_
          exact lt_trans (Metric.mem_ball.1 (hzs_ball n)) (by
            have : min (δ / 2) (1 / (n + 1 : ℝ)) ≤ δ / 2 := min_le_left _ _
            linarith))
    have hnorm : ‖fderiv ℝ F (zs n)‖ ≤ (K' : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ hnhds hK'
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  rcases IsCompact.tendsto_subseq
      (isCompact_closedBall (x := (0 : Operator)) (r := (K' : ℝ))) hderiv_mem with
    ⟨A, -, φ, hφmono, hφtendsto⟩
  refine ⟨A, ?_⟩
  -- The convergent derivative subsequence realizes a raw generator at `y`.
  refine ⟨zs ∘ φ, hzs_tendsto.comp hφmono.tendsto_atTop, ?_, hφtendsto⟩
  intro n
  exact hzs_diff (φ n)

/-- Helper for Chapter14 Lemma 14.8.2: every nearby generalized Jacobian is nonempty. -/
lemma generalizedJacobianNonempty_of_closedBallLipschitzNear
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2)) :
    ((∂ F) y).Nonempty := by
  rcases generalizedJacobianGeneratorSetNonempty_of_closedBallLipschitzNear
      (F := F) (x := x) (ε := ε) (K := K) hε hK hy with ⟨A, hA⟩
  exact ⟨A, mem_generalizedJacobian_of_mem_generatorSet hA⟩

/-- Helper for Chapter14 Lemma 14.8.2: a shell around a point `y` inside the small
`(2m + 2)⁻¹`-ball around `x` transports into the `m`th shell around `x`. -/
lemma rawShellTransportAtDoubleIndex
    {F : Point → Point} {x y : Point} (m : ℕ)
    (hy : y ∈ Metric.ball x (1 / ((2 * m + 1) + 1 : ℝ))) :
    closure (nearbyDerivativeValues F y (1 / ((2 * m + 1) + 1 : ℝ))) ⊆
      closure (nearbyDerivativeValues F x (1 / (m + 1 : ℝ))) := by
  refine closure_mono ?_
  refine nearbyDerivativeValues_subset_of_dist_add_le ?_
  have hy_le :
      dist y x ≤ 1 / ((2 * m + 1) + 1 : ℝ) :=
    le_of_lt (Metric.mem_ball.1 hy)
  calc
    dist y x + 1 / ((2 * m + 1) + 1 : ℝ)
        ≤ 1 / ((2 * m + 1) + 1 : ℝ) + 1 / ((2 * m + 1) + 1 : ℝ) := by
          gcongr
    _ = 1 / (m + 1 : ℝ) := reciprocal_doubleIndex_add_eq m

/-- Helper for Chapter14 Lemma 14.8.2: every raw generator can be realized at any positive
radius by a differentiability point whose derivative is simultaneously close to the generator. -/
lemma exists_differentiabilityPoint_close_of_mem_generalizedJacobianGeneratorSet
    {F : Point → Point} {x : Point} {A : Operator}
    (hA : A ∈ generalizedJacobianGeneratorSet F x)
    {r : ℝ} (hr : 0 < r) :
    ∃ z : Point,
      z ∈ Metric.ball x r ∧
      DifferentiableAt ℝ F z ∧
      fderiv ℝ F z ∈ Metric.ball A r := by
  rcases hA with ⟨xs, hxs, hdiff, hlim⟩
  have hx_event :
      ∀ᶠ i in Filter.atTop, xs i ∈ Metric.ball x r :=
    hxs (Metric.ball_mem_nhds x hr)
  have hA_event :
      ∀ᶠ i in Filter.atTop, fderiv ℝ F (xs i) ∈ Metric.ball A r :=
    hlim (Metric.ball_mem_nhds A hr)
  have h_event :
      ∀ᶠ i in Filter.atTop,
        xs i ∈ Metric.ball x r ∧
          DifferentiableAt ℝ F (xs i) ∧
            fderiv ℝ F (xs i) ∈ Metric.ball A r := by
    -- Intersect the pointwise convergence-to-`x` and derivative convergence-to-`A` events.
    filter_upwards [hx_event, hA_event] with i hxi hAi
    exact ⟨hxi, hdiff i, hAi⟩
  rcases Filter.eventually_atTop.1 h_event with ⟨N, hN⟩
  refine ⟨xs N, ?_, ?_, ?_⟩
  · exact (hN N le_rfl).1
  · exact (hN N le_rfl).2.1
  · exact (hN N le_rfl).2.2

/-- Helper for Chapter14 Lemma 14.8.2: limits of nearby raw generators remain raw generators at
the center point. -/
lemma mem_generalizedJacobianGeneratorSet_of_tendsto
    {F : Point → Point} {x : Point}
    {ys : ℕ → Point} {As : ℕ → Operator} {A : Operator}
    (hys : Filter.Tendsto ys Filter.atTop (nhds x))
    (hAs : Filter.Tendsto As Filter.atTop (nhds A))
    (hmem : ∀ n, As n ∈ generalizedJacobianGeneratorSet F (ys n)) :
    A ∈ generalizedJacobianGeneratorSet F x := by
  -- Route correction: instead of reopening the shrinking-shell owner at every `n`, choose one
  -- differentiability point from each raw generator whose position and derivative are both
  -- `1 / (n + 1)`-close, then diagonalize those approximants directly.
  have hchoose :
      ∀ n : ℕ, ∃ z : Point,
        z ∈ Metric.ball (ys n) (1 / (n + 1 : ℝ)) ∧
        DifferentiableAt ℝ F z ∧
        fderiv ℝ F z ∈ Metric.ball (As n) (1 / (n + 1 : ℝ)) := by
    intro n
    have hr : 0 < (1 / (n + 1 : ℝ)) := by positivity
    exact
      exists_differentiabilityPoint_close_of_mem_generalizedJacobianGeneratorSet
        (hA := hmem n) hr
  choose zs hzs_mem hzs_diff hzs_close using hchoose
  refine ⟨zs, ?_, hzs_diff, ?_⟩
  · -- The chosen differentiability points stay `1 / (n + 1)`-close to `ys n`, so they inherit
    -- the convergence `ys n → x`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases (Metric.tendsto_atTop.1 hys) (ε / 2) (by linarith) with ⟨N₁, hN₁⟩
    rcases (Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))) (ε / 2) (by linarith) with
      ⟨N₂, hN₂⟩
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn
    have hys_lt : dist (ys n) x < ε / 2 :=
      hN₁ n (le_trans (le_max_left _ _) hn)
    have hrad_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) := by positivity
    have hrad_abs : |(1 / (n + 1 : ℝ)) - 0| < ε / 2 := by
      simpa [Real.dist_eq] using hN₂ n (le_trans (le_max_right _ _) hn)
    have hrad_lt : 1 / (n + 1 : ℝ) < ε / 2 := by
      rw [sub_zero, abs_of_nonneg hrad_nonneg] at hrad_abs
      exact hrad_abs
    have hzs_lt : dist (zs n) (ys n) < 1 / (n + 1 : ℝ) :=
      Metric.mem_ball.1 (hzs_mem n)
    calc
      dist (zs n) x ≤ dist (zs n) (ys n) + dist (ys n) x := dist_triangle _ _ _
      _ < 1 / (n + 1 : ℝ) + ε / 2 := add_lt_add hzs_lt hys_lt
      _ < ε := by linarith
  · -- The derivatives stay `1 / (n + 1)`-close to `As n`, so they inherit the convergence
    -- `As n → A`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases (Metric.tendsto_atTop.1 hAs) (ε / 2) (by linarith) with ⟨N₁, hN₁⟩
    rcases (Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))) (ε / 2) (by linarith) with
      ⟨N₂, hN₂⟩
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn
    have hAs_lt : dist (As n) A < ε / 2 :=
      hN₁ n (le_trans (le_max_left _ _) hn)
    have hrad_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) := by positivity
    have hrad_abs : |(1 / (n + 1 : ℝ)) - 0| < ε / 2 := by
      simpa [Real.dist_eq] using hN₂ n (le_trans (le_max_right _ _) hn)
    have hrad_lt : 1 / (n + 1 : ℝ) < ε / 2 := by
      rw [sub_zero, abs_of_nonneg hrad_nonneg] at hrad_abs
      exact hrad_abs
    have hzs_lt : dist (fderiv ℝ F (zs n)) (As n) < 1 / (n + 1 : ℝ) :=
      Metric.mem_ball.1 (hzs_close n)
    calc
      dist (fderiv ℝ F (zs n)) A
          ≤ dist (fderiv ℝ F (zs n)) (As n) + dist (As n) A := dist_triangle _ _ _
      _ < 1 / (n + 1 : ℝ) + ε / 2 := add_lt_add hzs_lt hAs_lt
      _ < ε := by linarith

/-- Helper for Chapter14 Lemma 14.8.2: if an open set already contains the raw generator set at
`x`, then it eventually contains every nearby raw generator set along a sequence converging to
`x` inside the half-radius ball. -/
lemma eventually_generatorSet_subset_of_isOpen_of_tendsto
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {U : Set Operator}
    (hU : IsOpen U)
    (hUx : generalizedJacobianGeneratorSet F x ⊆ U)
    {ys : ℕ → Point}
    (hys : Filter.Tendsto ys Filter.atTop (nhds x))
    (hys_ball : ∀ n, ys n ∈ Metric.ball x (ε / 2)) :
    ∀ᶠ n in Filter.atTop, generalizedJacobianGeneratorSet F (ys n) ⊆ U := by
  by_contra h_eventual
  have h_freq :
      ∃ᶠ n in Filter.atTop, ¬ generalizedJacobianGeneratorSet F (ys n) ⊆ U := by
    rwa [Filter.not_eventually] at h_eventual
  rcases Filter.extraction_of_frequently_atTop h_freq with ⟨φ, hφmono, hφbad⟩
  have hA_choice :
      ∀ n, ∃ A : Operator, A ∈ generalizedJacobianGeneratorSet F (ys (φ n)) ∧ A ∉ U := by
    intro n
    -- Choose one bad raw generator from each index where subset containment fails.
    simpa [Set.not_subset_iff_exists_mem_notMem] using hφbad n
  choose As hAs_mem hAs_notMem using hA_choice
  have hAs_ball :
      ∀ n, As n ∈ Metric.closedBall (0 : Operator) (K : ℝ) := by
    intro n
    -- Every bad generator still lies in the common operator closed ball from the Lipschitz shell.
    exact
      mem_closedBall_generalizedJacobianGeneratorSet_of_closedBallLipschitzNear
        (F := F) (x := x) (ε := ε) (K := K) hε hK (hys_ball (φ n)) (hAs_mem n)
  rcases IsCompact.tendsto_subseq
      (isCompact_closedBall (x := (0 : Operator)) (r := (K : ℝ))) hAs_ball with
    ⟨A, -, ψ, hψmono, hA_tendsto⟩
  have hys_sub :
      Filter.Tendsto (ys ∘ φ ∘ ψ) Filter.atTop (nhds x) := by
    -- Strictly monotone extractions preserve convergence to the base point.
    exact hys.comp (hφmono.tendsto_atTop.comp hψmono.tendsto_atTop)
  have hAs_mem_sub :
      ∀ n, As (ψ n) ∈ generalizedJacobianGeneratorSet F ((ys ∘ φ ∘ ψ) n) := by
    intro n
    simpa [Function.comp] using hAs_mem (ψ n)
  have hA_mem :
      A ∈ generalizedJacobianGeneratorSet F x :=
    mem_generalizedJacobianGeneratorSet_of_tendsto
      (hys := hys_sub) (hAs := hA_tendsto) hAs_mem_sub
  have hA_in_U : A ∈ U := hUx hA_mem
  have hAs_eventually :
      ∀ᶠ n in Filter.atTop, As (ψ n) ∈ U :=
    hA_tendsto (hU.mem_nhds hA_in_U)
  rcases Filter.eventually_atTop.1 hAs_eventually with ⟨N, hN⟩
  exact hAs_notMem (ψ N) (hN N le_rfl)

/-- Helper for Chapter14 Lemma 14.8.2: the closure of a nearby public generalized Jacobian is
compact because the raw generator set is compact and its convex hull is totally bounded. -/
lemma isCompact_closure_generalizedJacobian_of_closedBallLipschitzNear
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {y : Point}
    (hy : y ∈ Metric.ball x (ε / 2)) :
    IsCompact (closure ((∂ F) y)) := by
  -- Rewrite the closure of `(∂ F) y` as the closed convex hull of the compact raw generator set.
  rw [generalizedJacobian_eq_convexHull_generatorSet, ← closedConvexHull_eq_closure_convexHull]
  have hcompactGenerator :
      IsCompact (generalizedJacobianGeneratorSet F y) :=
    isCompact_generalizedJacobianGeneratorSet_of_closedBallLipschitzNear
      (F := F) (x := x) (ε := ε) (K := K) hε hK hy
  have htotallyBounded :
      TotallyBounded (closedConvexHull ℝ (generalizedJacobianGeneratorSet F y)) := by
    rw [closedConvexHull_eq_closure_convexHull]
    exact (totallyBounded_closure).2 <|
      totallyBounded_convexHull Operator hcompactGenerator.totallyBounded
  -- Closedness of the closed convex hull upgrades total boundedness to compactness.
  exact htotallyBounded.isCompact_of_isClosed isClosed_closedConvexHull

/-- Helper for Chapter14 Lemma 14.8.2: an open convex neighborhood of the raw generator set at
`x` eventually contains the whole public generalized Jacobian along any nearby convergent
sequence. -/
lemma eventually_generalizedJacobian_subset_of_isOpenConvex_of_tendsto
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {U : Set Operator}
    (hU : IsOpen U)
    (hUconv : Convex ℝ U)
    (hUx : generalizedJacobianGeneratorSet F x ⊆ U)
    {ys : ℕ → Point}
    (hys : Filter.Tendsto ys Filter.atTop (nhds x))
    (hys_ball : ∀ n, ys n ∈ Metric.ball x (ε / 2)) :
    ∀ᶠ n in Filter.atTop, (∂ F) (ys n) ⊆ U := by
  -- First transport the open-set containment to the raw generator owner.
  filter_upwards
      [eventually_generatorSet_subset_of_isOpen_of_tendsto
        (F := F) (x := x) (ε := ε) (K := K) hε hK hU hUx hys hys_ball] with n hn
  intro V hV
  -- Then lift from generators to the public owner through the convexity of `U`.
  rw [generalizedJacobian_eq_convexHull_generatorSet] at hV
  exact (convexHull_min hn hUconv) hV

/-- Helper for Chapter14 Lemma 14.8.2: limits of nearby public generalized-Jacobian elements lie
in the closure of the base-point generalized Jacobian. -/
lemma mem_closure_generalizedJacobian_of_tendsto_of_mem_ball
    {F : Point → Point} {x : Point} {ε : ℝ} {K : NNReal}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F (Metric.closedBall x ε))
    {ys : ℕ → Point} {Vs : ℕ → Operator} {V : Operator}
    (hys : Filter.Tendsto ys Filter.atTop (nhds x))
    (hVs : Filter.Tendsto Vs Filter.atTop (nhds V))
    (hys_ball : ∀ n, ys n ∈ Metric.ball x (ε / 2))
    (hmem : ∀ n, Vs n ∈ (∂ F) (ys n)) :
    V ∈ closure ((∂ F) x) := by
  by_contra hV
  have hclosure_convex : Convex ℝ (closure ((∂ F) x)) := by
    -- The public generalized Jacobian is convex, and closure preserves convexity.
    rw [generalizedJacobian_eq_convexHull_generatorSet]
    exact (convex_convexHull ℝ (generalizedJacobianGeneratorSet F x)).closure
  obtain ⟨f, u, hlt_closure, hlt_limit⟩ :=
    geometric_hahn_banach_closed_point hclosure_convex isClosed_closure hV
  let U : Set Operator := {A : Operator | f A < u}
  have hU_open : IsOpen U := by
    -- The separating halfspace is open because `f` is continuous.
    exact isOpen_lt f.continuous continuous_const
  have hU_convex : Convex ℝ U := by
    -- Linearity of `f` makes the strict halfspace convex.
    intro A hA B hB a b ha hb hab
    have hsep :
        a * f A + b * f B < a * u + b * u := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by nlinarith
        simpa [U, ha0, hb1] using hB
      · by_cases hb0 : b = 0
        · have ha1 : a = 1 := by nlinarith
          simpa [U, ha1, hb0] using hA
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
          have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
          have hA' : a * f A < a * u := by
            exact mul_lt_mul_of_pos_left hA ha_pos
          have hB' : b * f B < b * u := by
            exact mul_lt_mul_of_pos_left hB hb_pos
          exact add_lt_add hA' hB'
    calc
      f (a • A + b • B) = a * f A + b * f B := by simp [map_add, map_smul]
      _ < a * u + b * u := hsep
      _ = (a + b) * u := by ring
      _ = u := by rw [hab, one_mul]
  have hgenerator_subset :
      generalizedJacobianGeneratorSet F x ⊆ U := by
    intro A hA
    -- Every raw generator lies in `(∂ F) x`, hence in its closure and therefore in the
    -- separating halfspace.
    exact hlt_closure A <| subset_closure <|
      mem_generalizedJacobian_of_mem_generatorSet hA
  have hVs_in_U :
      ∀ᶠ n in Filter.atTop, Vs n ∈ U := by
    filter_upwards
        [eventually_generalizedJacobian_subset_of_isOpenConvex_of_tendsto
          (F := F) (x := x) (ε := ε) (K := K) hε hK hU_open hU_convex
          hgenerator_subset hys hys_ball] with n hn
    exact hn (hmem n)
  let W : Set Operator := {A : Operator | u < f A}
  have hW_open : IsOpen W := by
    -- The opposite strict halfspace is also open, so convergence to `V` eventually enters it.
    exact isOpen_lt continuous_const f.continuous
  have hV_in_W : V ∈ W := hlt_limit
  have hVs_in_W :
      ∀ᶠ n in Filter.atTop, Vs n ∈ W :=
    hVs (hW_open.mem_nhds hV_in_W)
  have hfalse : ∀ᶠ n in (Filter.atTop : Filter ℕ), False := by
    -- No operator can satisfy both strict inequalities at once.
    filter_upwards [hVs_in_U, hVs_in_W] with n hnU hnW
    exact (not_lt_of_gt (by simpa [W] using hnW)) (by simpa [U] using hnU)
  rcases (Filter.eventually_atTop.1 hfalse) with ⟨N, hN⟩
  exact hN N le_rfl

/-- Helper for Chapter14 Lemma 14.8.2: once a sequence of operators converges to an invertible
limit, the operators are eventually invertible and their inverse norms are uniformly bounded. -/
lemma eventually_isInvertible_and_normInverse_le_of_tendsto
    {As : ℕ → Operator} {A : Operator}
    (hAs : Tendsto As atTop (nhds A))
    (hA : A.IsInvertible) :
    ∀ᶠ n in atTop, (As n).IsInvertible ∧ ‖(As n).inverse‖ ≤ ‖A.inverse‖ + 1 := by
  have hInvertibleOpen : IsOpen {B : Operator | B.IsInvertible} := by
    have hEq : {B : Operator | B.IsInvertible} = {B : Operator | IsUnit B} := by
      ext B
      constructor
      · intro hB
        rcases hB with ⟨e, rfl⟩
        exact e.toUnit.isUnit
      · intro hB
        rcases hB with ⟨u, hu⟩
        exact ⟨ContinuousLinearEquiv.ofUnit u, by
          change ((u : Point →L[ℝ] Point) : Operator) = B
          simpa using hu⟩
    rw [hEq]
    exact Units.isOpen
  have hEventuallyInvertible :
      ∀ᶠ n in atTop, (As n).IsInvertible :=
    hAs (hInvertibleOpen.mem_nhds hA)
  have hInverseContinuous :
      ContinuousAt (fun B : Operator ↦ B.inverse) A := by
    exact (hA.contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)).continuousAt
  have hEventuallyClose :
      ∀ᶠ n in atTop, ‖(As n).inverse - A.inverse‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using
      (hInverseContinuous.tendsto.comp hAs)
        (Metric.ball_mem_nhds A.inverse zero_lt_one)
  filter_upwards [hEventuallyInvertible, hEventuallyClose] with n hninv hnclose
  refine ⟨hninv, ?_⟩
  -- Compare the inverse norm to the limit inverse through a one-step triangle inequality.
  have hnorm :
      ‖(As n).inverse‖ ≤ ‖(As n).inverse - A.inverse‖ + ‖A.inverse‖ := by
    calc
      ‖(As n).inverse‖ = ‖((As n).inverse - A.inverse) + A.inverse‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖(As n).inverse - A.inverse‖ + ‖A.inverse‖ := norm_add_le _ _
  have hlt :
      ‖(As n).inverse‖ < ‖A.inverse‖ + 1 := by
    have hrhs :
        ‖(As n).inverse - A.inverse‖ + ‖A.inverse‖ < 1 + ‖A.inverse‖ := by
      linarith
    exact lt_of_le_of_lt hnorm (by simpa [add_comm, add_left_comm, add_assoc] using hrhs)
  exact le_of_lt hlt

/-- Chapter14 Lemma 14.8.2: if `F` is Lipschitz on some closed ball centered at `x` and every
`V ∈ (∂ F) x = ∂F(x)` is nonsingular, then there is a positive-radius neighborhood of `x` and a
constant `C` such that every nearby generalized Jacobian `(∂ F) y = ∂F(y)` is nonempty, and
every `V ∈ (∂ F) y` with `y` in that neighborhood is nonsingular and satisfies `(14.8.20)`:
`‖V.inverse‖ ≤ C`. -/
theorem exists_ball_bound_of_generalizedJacobian_nonsingularAt
    (F : Point → Point)
    (x : Point)
    (h_local : LocallyLipschitzAt F x)
    (h_nonsingular :
      ∀ ⦃V : Operator⦄, V ∈ (∂ F) x → V.IsInvertible) :
    ∃ r > 0, ∃ C : ℝ,
      ∀ ⦃y : Point⦄, y ∈ Metric.ball x r →
        ((∂ F) y).Nonempty ∧
          ∀ ⦃V : Operator⦄, V ∈ (∂ F) y →
            V.IsInvertible ∧ ‖V.inverse‖ ≤ C := by
  -- Start from the closed-ball Lipschitz witness supplied by the local regularity hypothesis.
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  have hbound_near :
      ∀ ⦃y : Point⦄, y ∈ Metric.ball x (ε / 2) →
        ∀ ⦃V : Operator⦄, V ∈ (∂ F) y →
          V ∈ Metric.closedBall (0 : Operator) (K : ℝ) := by
    intro y hy V hV
    exact
      mem_closedBall_generalizedJacobian_of_closedBallLipschitzNear
        (F := F) (x := x) (ε := ε) (K := K) hε hK hy hV
  have hnonempty_near :
      ∀ ⦃y : Point⦄, y ∈ Metric.ball x (ε / 2) →
        ((∂ F) y).Nonempty := by
    intro y hy
    exact
      generalizedJacobianNonempty_of_closedBallLipschitzNear
        (F := F) (x := x) (ε := ε) (K := K) hε hK hy
  by_contra hfail
  have hbadChoice :
      ∀ n : ℕ,
        ∃ y : Point,
          y ∈ Metric.ball x (min (ε / 2) (1 / (n + 1 : ℝ))) ∧
            ∃ V : Operator,
              V ∈ (∂ F) y ∧
                (¬ V.IsInvertible ∨ (n : ℝ) < ‖V.inverse‖) := by
    intro n
    let r : ℝ := min (ε / 2) (1 / (n + 1 : ℝ))
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hnoC :
        ¬ ∃ C : ℝ,
            ∀ ⦃y : Point⦄, y ∈ Metric.ball x r →
              ((∂ F) y).Nonempty ∧
                ∀ ⦃V : Operator⦄, V ∈ (∂ F) y →
                  V.IsInvertible ∧ ‖V.inverse‖ ≤ C := by
      intro hC
      exact hfail ⟨r, hr, hC⟩
    by_contra hbad
    push Not at hbad
    -- If the `n`th shrinking ball had no bad operator, the theorem would already hold there with
    -- the concrete bound `C = n`.
    apply hnoC
    refine ⟨(n : ℝ), ?_⟩
    intro y hy
    have hyNear : y ∈ Metric.ball x (ε / 2) := by
      exact Metric.mem_ball.2 <| lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_left _ _)
    refine ⟨hnonempty_near hyNear, ?_⟩
    intro V hV
    exact hbad y hy V hV
  choose ys hys_mem Vs hVs_mem hVs_bad using hbadChoice
  have hys_near : ∀ n, ys n ∈ Metric.ball x (ε / 2) := by
    intro n
    exact Metric.mem_ball.2 <| lt_of_lt_of_le (Metric.mem_ball.1 (hys_mem n)) (min_le_left _ _)
  have hys_tendsto : Tendsto ys atTop (nhds x) := by
    -- The radii `min (ε / 2) (1 / (n + 1))` shrink to `0`, so the bad base points converge to `x`.
    rw [Metric.tendsto_atTop]
    intro ρ hρ
    rcases (Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
        (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (nhds 0))) ρ hρ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hN' : |(1 / (n + 1 : ℝ))| < ρ := by
      simpa [Real.dist_eq] using hN n hn
    have hradius : 1 / (n + 1 : ℝ) < ρ := (abs_lt.mp hN').2
    have hdist :
        dist (ys n) x < min (ε / 2) (1 / (n + 1 : ℝ)) :=
      Metric.mem_ball.1 (hys_mem n)
    exact lt_of_lt_of_le hdist <| le_trans (min_le_right _ _) hradius.le
  have hVs_ball :
      ∀ n, Vs n ∈ Metric.closedBall (0 : Operator) (K : ℝ) := by
    intro n
    exact hbound_near (hys_near n) (hVs_mem n)
  rcases IsCompact.tendsto_subseq
      (isCompact_closedBall (x := (0 : Operator)) (r := (K : ℝ))) hVs_ball with
    ⟨V, -, φ, hφmono, hV_tendsto⟩
  have hys_sub_tendsto :
      Tendsto (ys ∘ φ) atTop (nhds x) := by
    -- Strictly monotone extractions preserve convergence of the bad base points.
    exact hys_tendsto.comp hφmono.tendsto_atTop
  have hys_sub_ball : ∀ n, (ys ∘ φ) n ∈ Metric.ball x (ε / 2) := by
    intro n
    simpa [Function.comp] using hys_near (φ n)
  have hVs_sub_mem : ∀ n, (Vs ∘ φ) n ∈ (∂ F) ((ys ∘ φ) n) := by
    intro n
    simpa [Function.comp] using hVs_mem (φ n)
  have hε2 : 0 < ε / 2 := by
    linarith
  have hcompact_x : IsCompact ((∂ F) x) :=
    isCompact_generalizedJacobian_of_closedBallLipschitzNear
      (F := F) (x := x) (ε := ε) (K := K) hε hK (Metric.mem_ball_self hε2)
  have hV_mem_closure : V ∈ closure ((∂ F) x) :=
    mem_closure_generalizedJacobian_of_tendsto_of_mem_ball
      (F := F) (x := x) (ε := ε) (K := K) hε hK
      hys_sub_tendsto hV_tendsto hys_sub_ball hVs_sub_mem
  have hV_mem : V ∈ (∂ F) x := by
    simpa [hcompact_x.isClosed.closure_eq] using hV_mem_closure
  have hV_inv : V.IsInvertible := h_nonsingular hV_mem
  have hEventuallyGood :
      ∀ᶠ n in atTop,
        ((Vs ∘ φ) n).IsInvertible ∧ ‖((Vs ∘ φ) n).inverse‖ ≤ ‖V.inverse‖ + 1 :=
    eventually_isInvertible_and_normInverse_le_of_tendsto
      (As := Vs ∘ φ) (A := V) hV_tendsto hV_inv
  rcases Filter.eventually_atTop.1 hEventuallyGood with ⟨N₁, hN₁⟩
  let C0 : ℝ := ‖V.inverse‖ + 1
  rcases exists_nat_gt C0 with ⟨N₂, hN₂⟩
  let N : ℕ := max N₁ N₂
  have hgood :
      ((Vs ∘ φ) N).IsInvertible ∧ ‖((Vs ∘ φ) N).inverse‖ ≤ C0 := by
    simpa [Function.comp, C0] using hN₁ N (le_max_left _ _)
  have hbad : ¬ (Vs (φ N)).IsInvertible ∨ (φ N : ℝ) < ‖(Vs (φ N)).inverse‖ :=
    hVs_bad (φ N)
  cases hbad with
  | inl hnotinv =>
      exact hnotinv (by simpa [Function.comp] using hgood.1)
  | inr hlarge =>
      have hphi_ge : N ≤ φ N := hφmono.id_le N
      have hlarge' : (N : ℝ) < ‖(Vs (φ N)).inverse‖ := by
        exact lt_of_le_of_lt (by exact_mod_cast hphi_ge) hlarge
      have hsmall : ‖(Vs (φ N)).inverse‖ ≤ C0 := by
        simpa [Function.comp, C0] using hgood.2
      have hN_lt_C0 : (N : ℝ) < C0 :=
        lt_of_lt_of_le hlarge' hsmall
      have hC0_lt_N : C0 < (N : ℝ) := by
        have hN₂_le_N : (N₂ : ℝ) ≤ N := by
          exact_mod_cast (le_max_right N₁ N₂)
        exact lt_of_lt_of_le hN₂ hN₂_le_N
      exact (not_lt_of_ge (le_of_lt hC0_lt_N)) hN_lt_C0

end Chapter14Lemma1482
