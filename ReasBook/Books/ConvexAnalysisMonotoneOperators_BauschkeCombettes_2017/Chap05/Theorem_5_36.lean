/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Lemma_5_31

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The closed convex hull of the tail `{y n | m ≤ n}` of a sequence `y`. -/
def tailClosedConvexHull (y : ℕ → H) (m : ℕ) : Set H :=
  closedConvexHull ℝ (y '' Set.Ici m)

-- Proof sketch: if `m ≤ n`, then `y n` belongs to the image `y '' Set.Ici m`; this image is
-- contained in its closed convex hull.
/-- Every term of a sequence tail belongs to the corresponding tail closed convex hull. -/
theorem mem_tailClosedConvexHull (y : ℕ → H) {m n : ℕ} (hmn : m ≤ n) :
    y n ∈ tailClosedConvexHull y m := by
  -- The tail term already lies in the generating image set, hence in its closed convex hull.
  exact subset_closedConvexHull ⟨n, hmn, rfl⟩

/-- Helper for Theorem 5.36: quasi-Fejér monotonicity in the sense of Definition 5.32 makes each
distance sequence `n ↦ ‖y n - z‖` converge. -/
private theorem quasiFejerMonotone_norm_tendsto
    {C : Set H} {y : ℕ → H} (hy : QuasiFejerMonotone C y) {z : H} (hz : z ∈ C) :
    ∃ l : ℝ, Tendsto (fun n ↦ ‖y n - z‖) atTop (𝓝 l) := by
  rcases hy.exists_summable_sqdist_error z hz with ⟨ε, hεsumm, hstep⟩
  let a : ℕ → NNReal := fun n ↦ ⟨‖y n - z‖ ^ 2, sq_nonneg _⟩
  have hrec : ∀ n : ℕ, a (n + 1) + 0 ≤ (1 + 0) * a n + ε n := by
    intro n
    -- The defining quasi-Fejér estimate already has the perturbed-descent shape from Lemma 5.31.
    norm_num [a]
    exact hstep n
  rcases
      tendsto_and_summable_of_summable_perturbed_descent
        (α := a) (β := fun _ ↦ 0) (γ := fun _ ↦ 0) (ε := ε)
        summable_zero hεsumm hrec with
    ⟨⟨l, ha⟩, _⟩
  refine ⟨Real.sqrt l, ?_⟩
  have hareal :
      Tendsto (fun n ↦ ((a n : NNReal) : ℝ)) atTop (𝓝 (l : ℝ)) :=
    (NNReal.tendsto_coe').2 ⟨l.2, ha⟩
  have hsqrt :
      Tendsto (fun n ↦ Real.sqrt (((a n : NNReal) : ℝ))) atTop (𝓝 (Real.sqrt (l : ℝ))) :=
    (Real.continuous_sqrt.tendsto _).comp hareal
  -- Taking square roots turns convergence of squared distances back into convergence of norms.
  have hsqrt_apply :
      (fun n ↦ Real.sqrt (((a n : NNReal) : ℝ))) = (fun n ↦ ‖y n - z‖) := by
    funext n
    change Real.sqrt (‖y n - z‖ ^ 2) = ‖y n - z‖
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt_apply] at hsqrt
  exact hsqrt

/-- Helper for Theorem 5.36: a finite prefix can be discarded once the remaining tail has a common
norm bound. -/
private lemma bounded_range_of_eventually_norm_le
    {x : ℕ → H} {R : ℝ} (hR : ∀ᶠ n in atTop, ‖x n‖ ≤ R) :
    Bornology.IsBounded (Set.range x) := by
  rw [eventually_atTop] at hR
  rcases hR with ⟨N, hN⟩
  let s₀ : Set H := {y | ∃ n < N, x n = y}
  let s₁ : Set H := Set.range fun n : ℕ ↦ x (n + N)
  have hs₀_finite : s₀.Finite := by
    classical
    have hs₀_eq : s₀ = x '' {n : ℕ | n < N} := by
      ext y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
    rw [hs₀_eq]
    exact (Set.finite_lt_nat N).image x
  have hs₁_bounded : Bornology.IsBounded s₁ := by
    refine (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : H) R)).subset ?_
    rintro y ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hN (n + N) (Nat.le_add_left N n)
  have hrange_subset : Set.range x ⊆ s₀ ∪ s₁ := by
    rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr ⟨n - N, by simp [Nat.sub_add_cancel (Nat.le_of_not_lt hn)]⟩
  exact (hs₀_finite.isBounded.union hs₁_bounded).subset hrange_subset

/-- Helper for Theorem 5.36: boundedness of `range y` propagates to every tail closed convex hull
of `y`. -/
private lemma tailClosedConvexHull_bounded
    {y : ℕ → H} (hy_bounded : Bornology.IsBounded (Set.range y)) (m : ℕ) :
    Bornology.IsBounded (tailClosedConvexHull y m) := by
  rcases isBounded_iff_forall_norm_le.mp hy_bounded with ⟨R, hR⟩
  have hsubset_ball : tailClosedConvexHull y m ⊆ Metric.closedBall (0 : H) R := by
    -- Minimality of the closed convex hull transfers the ball bound from the tail image.
    refine closedConvexHull_min ?_ (convex_closedBall (0 : H) R) Metric.isClosed_closedBall
    rintro _ ⟨n, hn, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR _ (Set.mem_range_self n)
  exact Metric.isBounded_closedBall.subset hsubset_ball

/-- Helper for Theorem 5.36: asymptotic proximity to a bounded nonempty set forces the whole
sequence to be norm-bounded. -/
private lemma bounded_range_of_infDist_tendsto_zero_of_nonempty_bounded
    {x : ℕ → H} {S : Set H} (hS_nonempty : S.Nonempty) (hS_bounded : Bornology.IsBounded S)
    (hdist : Tendsto (fun n ↦ Metric.infDist (x n) S) atTop (𝓝 0)) :
    Bornology.IsBounded (Set.range x) := by
  rcases isBounded_iff_forall_norm_le.mp hS_bounded with ⟨R, hR⟩
  have hsmall : ∀ᶠ n in atTop, Metric.infDist (x n) S < 1 := by
    simpa using hdist.eventually (Iio_mem_nhds zero_lt_one)
  have hnorm : ∀ᶠ n in atTop, ‖x n‖ ≤ R + 1 := by
    filter_upwards [hsmall] with n hn
    rcases (Metric.infDist_lt_iff hS_nonempty).mp hn with ⟨y, hyS, hy⟩
    have hyR : ‖y‖ ≤ R := hR _ hyS
    have hxy : ‖x n - y‖ < 1 := by
      simpa [dist_eq_norm] using hy
    -- A nearby point of the bounded set gives the required norm bound.
    calc
      ‖x n‖ = ‖(x n - y) + y‖ := by abel_nf
      _ ≤ ‖x n - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  exact bounded_range_of_eventually_norm_le hnorm

/-- Helper for Theorem 5.36: if a closed convex slab contains the whole tail of `y`, then it also
contains the corresponding tail closed convex hull. -/
private lemma tailClosedConvexHull_subset_of_tail_mem
    {y : ℕ → H} {Q : Set H} {m : ℕ} (hQ : ∀ n : ℕ, m ≤ n → y n ∈ Q)
    (hQ_convex : Convex ℝ Q) (hQ_closed : IsClosed Q) :
    tailClosedConvexHull y m ⊆ Q := by
  -- Minimality of the closed convex hull closes the tail inclusion.
  refine closedConvexHull_min ?_ hQ_convex hQ_closed
  rintro _ ⟨n, hn, rfl⟩
  exact hQ n hn

/-- Helper for Theorem 5.36: once the tail closed convex hull lies in a slab centered at `ℓ`,
vanishing distance to that hull transfers the same scalar limit to `xₙ`. -/
private theorem eventually_inner_deviation_le_of_infDist_tailClosedConvexHull
    {xₙ yₙ : ℕ → H} {m : ℕ} {v : H} {ℓ ε : ℝ} (hε : 0 < ε)
    (hTail :
      ∀ n : ℕ, m ≤ n → inner ℝ (yₙ n) v ∈ Set.Icc (ℓ - ε) (ℓ + ε))
    (hdist :
      Tendsto (fun n ↦ Metric.infDist (xₙ n) (tailClosedConvexHull yₙ m)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, |inner ℝ (xₙ n) v - ℓ| ≤ ε * (‖v‖ + 1) := by
  let Q : Set H := (fun u : H ↦ inner ℝ u v) ⁻¹' Set.Icc (ℓ - ε) (ℓ + ε)
  have hQ_convex : Convex ℝ Q := by
    -- The slab is the preimage of an interval under a continuous linear functional.
    simpa [Q] using
      (convex_Icc (ℓ - ε) (ℓ + ε)).is_linear_preimage
        (f := fun u : H ↦ inner ℝ u v)
        { map_add := by
            intro x y
            rw [inner_add_left]
          map_smul := by
            intro a x
            simp [smul_eq_mul, real_inner_smul_left] }
  have hQ_closed : IsClosed Q := by
    -- Closedness is inherited from the closed interval in `ℝ`.
    simpa [Q] using
      isClosed_Icc.preimage (continuous_id.inner continuous_const)
  have htail_subset : tailClosedConvexHull yₙ m ⊆ Q := by
    -- The whole tail lies in the slab, so the tail closed convex hull lies there as well.
    refine tailClosedConvexHull_subset_of_tail_mem ?_ hQ_convex hQ_closed
    intro n hn
    simpa [Q] using hTail n hn
  have htail_nonempty : (tailClosedConvexHull yₙ m).Nonempty := by
    exact ⟨yₙ m, mem_tailClosedConvexHull yₙ le_rfl⟩
  have hsmall :
      ∀ᶠ n in atTop, Metric.infDist (xₙ n) Q < ε := by
    filter_upwards [hdist.eventually (Iio_mem_nhds hε)] with n hn
    exact lt_of_le_of_lt (Metric.infDist_le_infDist_of_subset htail_subset htail_nonempty) hn
  filter_upwards [hsmall] with n hn
  rcases (Metric.infDist_lt_iff (Set.Nonempty.mono htail_subset htail_nonempty)).mp hn with
    ⟨q, hqQ, hqdist⟩
  have hq_abs : |inner ℝ q v - ℓ| ≤ ε := by
    have hqIcc : inner ℝ q v ∈ Set.Icc (ℓ - ε) (ℓ + ε) := by
      simpa [Q] using hqQ
    rcases hqIcc with ⟨hq_lower, hq_upper⟩
    exact abs_le.mpr (by constructor <;> linarith)
  have hsplit :
      inner ℝ (xₙ n) v - ℓ = inner ℝ (xₙ n - q) v + (inner ℝ q v - ℓ) := by
    rw [inner_sub_left]
    ring
  -- Choose a nearby slab point `q`; its scalar coordinate is already within `ε` of `ℓ`.
  calc
    |inner ℝ (xₙ n) v - ℓ| = |inner ℝ (xₙ n - q) v + (inner ℝ q v - ℓ)| := by rw [hsplit]
    _ ≤ |inner ℝ (xₙ n - q) v| + |inner ℝ q v - ℓ| := by
          simpa [Real.norm_eq_abs] using
            (norm_add_le (inner ℝ (xₙ n - q) v) (inner ℝ q v - ℓ))
    _ ≤ ‖xₙ n - q‖ * ‖v‖ + ε := by
          gcongr
          exact abs_real_inner_le_norm _ _
    _ ≤ ε * ‖v‖ + ε := by
          have hnorm_lt : ‖xₙ n - q‖ < ε := by simpa [dist_eq_norm] using hqdist
          exact add_le_add (mul_le_mul_of_nonneg_right (le_of_lt hnorm_lt) (norm_nonneg _)) le_rfl
    _ = ε * (‖v‖ + 1) := by ring

/-- Helper for Theorem 5.36: the scalar coordinate of `xₙ` along `v` converges to the slab center
`ℓ` once the tail closed convex hulls asymptotically enter every such slab. -/
private theorem tendsto_inner_of_infDist_tailClosedConvexHull
    {xₙ yₙ : ℕ → H} {v : H} {ℓ : ℝ}
    (hslab :
      ∀ ε > 0, ∃ m : ℕ,
        ∀ n : ℕ, m ≤ n → inner ℝ (yₙ n) v ∈ Set.Icc (ℓ - ε) (ℓ + ε))
    (hdist :
      ∀ m : ℕ,
        Tendsto (fun n ↦ Metric.infDist (xₙ n) (tailClosedConvexHull yₙ m)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ inner ℝ (xₙ n) v) atTop (𝓝 ℓ) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  let ε : ℝ := δ / (2 * (‖v‖ + 1))
  have hε : 0 < ε := by
    positivity
  rcases hslab ε hε with ⟨m, hm⟩
  have hevent :
      ∀ᶠ n in atTop, |inner ℝ (xₙ n) v - ℓ| ≤ ε * (‖v‖ + 1) :=
    eventually_inner_deviation_le_of_infDist_tailClosedConvexHull hε hm (hdist m)
  rw [eventually_atTop] at hevent
  rcases hevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hbound : |inner ℝ (xₙ n) v - ℓ| ≤ ε * (‖v‖ + 1) := hN n hn
  have hconst : 0 < ‖v‖ + 1 := by positivity
  have hmul : ε * (‖v‖ + 1) = δ / 2 := by
    dsimp [ε]
    field_simp [hconst.ne']
  -- Shrinking the slab width by the fixed factor `2 * (‖v‖ + 1)` yields the metric `δ`-estimate.
  simpa [Real.dist_eq, hmul] using lt_of_le_of_lt hbound (by linarith)

-- Proof sketch: quasi-Fejér monotonicity of `yₙ` controls the geometry of the tail closed convex
-- hulls, the vanishing distance hypothesis forces `xₙ` asymptotically into those hulls, and the
-- weak sequential cluster-point hypothesis identifies the unique possible weak limit in `C`.
/-- Theorem 5.36: if `yₙ` is quasi-Fejér monotone with respect to a nonempty set `C`, the
distances from `xₙ` to the tail closed convex hulls
`tailClosedConvexHull yₙ m = overline (conv {yₖ | m ≤ k})` tend to `0` for every `m`, and every
weak sequential cluster point of `xₙ` lies in `C`, then `xₙ` converges weakly to a point of `C`.
-/
theorem tendsto_weakly_of_quasiFejerMonotone_of_tailClosedConvexHull_infDist_tendsto_zero
    {C : Set H} (hC : C.Nonempty) (xₙ yₙ : ℕ → H)
    (hyₙ :
      ∀ c ∈ C, ∃ ε : ℕ → NNReal, Summable ε ∧
        ∀ n : ℕ, ‖yₙ (n + 1) - c‖ ^ 2 ≤ ‖yₙ n - c‖ ^ 2 + ε n)
    (hdist :
      ∀ m : ℕ,
        Tendsto (fun n ↦ Metric.infDist (xₙ n) (tailClosedConvexHull yₙ m)) atTop (𝓝 0))
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H z) → z ∈ C) :
    ∃ z ∈ C, Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H z)) := by
  have hy_dist :
      ∀ z ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖yₙ n - z‖) atTop (𝓝 l) := by
    intro z hz
    -- The Definition 5.32 quasi-Fejér hypothesis gives convergence of each distance sequence.
    exact quasiFejerMonotone_norm_tendsto hyₙ hz
  have hy_bounded : Bornology.IsBounded (Set.range yₙ) := by
    rcases hC with ⟨z, hz⟩
    exact bounded_range_of_convergent_distance_to_point (hy_dist z hz)
  have hx_bounded : Bornology.IsBounded (Set.range xₙ) := by
    -- The bounded tail hull at `m = 0` traps `xₙ` asymptotically in a bounded neighborhood.
    refine bounded_range_of_infDist_tendsto_zero_of_nonempty_bounded
      ⟨yₙ 0, mem_tailClosedConvexHull yₙ le_rfl⟩
      (tailClosedConvexHull_bounded hy_bounded 0)
      (hdist 0)
  have hx_unique :
      ∀ x z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H z) →
        x = z := by
    intro x z hx hz
    have hxC : x ∈ C := hcluster x hx
    have hzC : z ∈ C := hcluster z hz
    rcases inner_tendsto_of_tendsto_dist_to_two_points hy_dist hxC hzC with ⟨ℓ, hℓ⟩
    let v : H := x - z
    have hslab :
        ∀ ε > 0, ∃ m : ℕ,
          ∀ n : ℕ, m ≤ n → inner ℝ (yₙ n) v ∈ Set.Icc (ℓ - ε) (ℓ + ε) := by
      intro ε hε
      rcases (Metric.tendsto_atTop.1 (by simpa [v] using hℓ)) ε hε with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      intro n hn
      have hdist_inner : dist (inner ℝ (yₙ n) v) ℓ < ε := hm n hn
      rw [Set.mem_Icc]
      have habs : |inner ℝ (yₙ n) v - ℓ| < ε := by
        simpa [Real.dist_eq] using hdist_inner
      have habs' : -ε ≤ inner ℝ (yₙ n) v - ℓ ∧ inner ℝ (yₙ n) v - ℓ ≤ ε :=
        abs_le.mp (le_of_lt habs)
      constructor <;> linarith
    have hx_inner :
        Tendsto (fun n ↦ inner ℝ (xₙ n) v) atTop (𝓝 ℓ) :=
      tendsto_inner_of_infDist_tailClosedConvexHull hslab hdist
    rcases hx.exists_subseq_tendsto with ⟨φx, hφx, hφx_tendsto⟩
    rcases hz.exists_subseq_tendsto with ⟨φz, hφz, hφz_tendsto⟩
    have hx_limit : inner ℝ x v = ℓ := by
      exact tendsto_nhds_unique
        (by simpa [v, Function.comp] using
          ((weakSpace_continuous_inner_right v).tendsto (toWeakSpace ℝ H x)).comp hφx_tendsto)
        (hx_inner.comp hφx.tendsto_atTop)
    have hz_limit : inner ℝ z v = ℓ := by
      exact tendsto_nhds_unique
        (by simpa [v, Function.comp] using
          ((weakSpace_continuous_inner_right v).tendsto (toWeakSpace ℝ H z)).comp hφz_tendsto)
        (hx_inner.comp hφz.tendsto_atTop)
    have hzero_sq : ‖x - z‖ ^ 2 = 0 := by
      -- Equality of the two scalar limits forces the norm of `x - z` to vanish.
      calc
        ‖x - z‖ ^ 2 = inner ℝ (x - z) (x - z) := by rw [real_inner_self_eq_norm_sq]
        _ = inner ℝ x (x - z) - inner ℝ z (x - z) := by rw [inner_sub_left]
        _ = 0 := by rw [hx_limit, hz_limit, sub_self]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero_sq))
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint xₙ).2
        ⟨hx_bounded, hx_unique⟩ with
    ⟨z, hz_tendsto⟩
  have hz_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H z) := by
    -- The full convergent sequence already witnesses its weak limit as a cluster point.
    exact ⟨id, strictMono_id, by simpa using hz_tendsto⟩
  exact ⟨z, hcluster z hz_cluster, hz_tendsto⟩

end
