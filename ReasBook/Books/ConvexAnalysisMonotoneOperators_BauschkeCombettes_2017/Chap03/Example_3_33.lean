/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology InnerProductSpace

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Example 3.33: distinct weighted orthonormal vectors satisfy the Pythagorean
distance identity. -/
private lemma scaled_orthonormal_dist_sq_eq_of_ne (e : ℕ → 𝓗) (he : Orthonormal ℝ e) (α : ℕ → ℝ)
    (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) {m n : ℕ} (hmn : m ≠ n) :
    ‖α m • e m - α n • e n‖ ^ 2 = α m ^ 2 + α n ^ 2 := by
  -- Positivity of the weights removes the absolute values in the norm computations.
  have hαm_nonneg : 0 ≤ α m := le_trans zero_le_one (hα_ge_one m)
  have hαn_nonneg : 0 ≤ α n := le_trans zero_le_one (hα_ge_one n)
  have hm : ‖α m • e m‖ = α m := by
    rw [norm_smul, he.norm_eq_one m, mul_one, Real.norm_of_nonneg hαm_nonneg]
  have hn : ‖α n • e n‖ = α n := by
    rw [norm_smul, he.norm_eq_one n, mul_one, Real.norm_of_nonneg hαn_nonneg]
  have hinner : inner ℝ (α m • e m) (α n • e n) = 0 := by
    rw [real_inner_smul_left, inner_smul_right, he.inner_eq_zero hmn, mul_zero, mul_zero]
  -- Then the real inner-product norm expansion collapses to a sum of squares.
  rw [norm_sub_sq_real, hm, hn, hinner]
  ring

/-- Helper for Example 3.33: distinct weighted orthonormal vectors stay more than unit distance
apart. -/
private lemma scaled_orthonormal_dist_gt_one_of_ne (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) {m n : ℕ} (hmn : m ≠ n) :
    1 < dist (α m • e m) (α n • e n) := by
  -- The squared distance is at least `2`, so the distance is strictly larger than `1`.
  have hsq :
      dist (α m • e m) (α n • e n) ^ 2 = α m ^ 2 + α n ^ 2 := by
    simpa [dist_eq_norm] using
      scaled_orthonormal_dist_sq_eq_of_ne e he α hα_ge_one hmn
  have hnonneg : 0 ≤ dist (α m • e m) (α n • e n) := dist_nonneg
  nlinarith [hsq, hα_ge_one m, hα_ge_one n]

/-- Helper for Example 3.33: every norm-convergent sequence in the weighted orthonormal range is
eventually constant. -/
private lemma eventually_constant_of_tendsto_scaled_orthonormal_range (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) {u : ℕ → 𝓗} {x : 𝓗}
    (hu : ∀ n : ℕ, u n ∈ Set.range (fun k ↦ α k • e k)) (hx : Tendsto u atTop (𝓝 x)) :
    ∃ N k, ∀ n ≥ N, u n = α k • e k := by
  -- Convergent sequences are Cauchy, so eventually every later term lies within distance `< 1`
  -- of a fixed anchor term.
  have hcauchy : CauchySeq u := hx.cauchySeq
  rcases (Metric.cauchySeq_iff'.1 hcauchy) 1 zero_lt_one with ⟨N, hN⟩
  rcases Set.mem_range.1 (hu N) with ⟨k, hk⟩
  refine ⟨N, k, ?_⟩
  intro n hn
  rcases Set.mem_range.1 (hu n) with ⟨kn, hkn⟩
  by_contra hneq
  have hdist_lt : dist (u n) (u N) < 1 := hN n hn
  have hkne : kn ≠ k := by
    intro hEq
    apply hneq
    calc
      u n = α kn • e kn := hkn.symm
      _ = α k • e k := by simp [hEq]
  have hdist_gt : 1 < dist (u n) (u N) := by
    rw [← hkn, ← hk]
    exact scaled_orthonormal_dist_gt_one_of_ne e he α hα_ge_one hkne
  linarith

/-- Helper for Example 3.33: the weighted orthonormal range is norm closed once distinct points are
uniformly separated. -/
private theorem isClosed_scaled_orthonormal_range (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) :
    IsClosed (Set.range (fun n ↦ α n • e n)) := by
  have hseqClosed : IsSeqClosed (Set.range (fun n ↦ α n • e n)) := by
    intro u x hu hx
    rcases eventually_constant_of_tendsto_scaled_orthonormal_range e he α hα_ge_one hu hx with
      ⟨N, k, hNk⟩
    have hconst : u =ᶠ[atTop] fun _ ↦ α k • e k := by
      exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ hNk n hn⟩
    have hxconst : Tendsto (fun _ : ℕ ↦ α k • e k) atTop (𝓝 x) := hx.congr' hconst
    have hxeq : x = α k • e k := tendsto_nhds_unique hxconst tendsto_const_nhds
    exact Set.mem_range.2 ⟨k, hxeq.symm⟩
  exact isSeqClosed_iff_isClosed.1 hseqClosed

variable [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
/-- Helper for Example 3.33: bounded weighted orthonormal values admit a constant subsequence of
their indices once the weights tend to `+∞`. -/
private lemma exists_constant_subseq_of_bounded_scaled_orthonormal_values (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_tendsto : Tendsto α atTop atTop) {n : ℕ → ℕ}
    (hbounded : Bornology.IsBounded (Set.range fun k ↦ α (n k) • e (n k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ j : ℕ, ∀ k, n (φ k) = j := by
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC : ∀ k, ‖α (n k) • e (n k)‖ ≤ C := by
    intro k
    exact le_trans (hC₀ _ (Set.mem_range_self k)) (le_max_left _ _)
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hα_tendsto) (C + 1)
  have hn_lt : ∀ k, n k < N := by
    intro k
    by_contra hkn
    have hlarge : C + 1 ≤ α (n k) := hN (n k) (le_of_not_gt hkn)
    have hα_nonneg : 0 ≤ α (n k) := by linarith
    have hnorm_eq : ‖α (n k) • e (n k)‖ = α (n k) := by
      rw [norm_smul, he.norm_eq_one (n k), mul_one, Real.norm_of_nonneg hα_nonneg]
    linarith [hC k, hlarge]
  let g : ℕ → {j : ℕ // j < N} := fun k ↦ ⟨n k, hn_lt k⟩
  obtain ⟨j, hjraw⟩ := Finite.exists_infinite_fiber g
  have hj : Set.Infinite {k : ℕ | g k = j} := by
    rw [Set.Infinite]
    intro hfinite
    let _ : Finite ↑(g ⁻¹' {j}) := hfinite.to_subtype
    exact Infinite.false hjraw
  refine ⟨Nat.nth (fun k ↦ g k = j), Nat.nth_strictMono hj, j.1, ?_⟩
  intro k
  have hk : g (Nat.nth (fun i ↦ g i = j) k) = j := Nat.nth_mem_of_infinite hj k
  exact congrArg Subtype.val hk

-- Proof sketch: a weakly convergent sequence in a Hilbert space is norm bounded. For a sequence in
-- `Set.range (fun n ↦ α n • e n)`, the norms are exactly the weights `α n`, so the divergence
-- `α n → +∞` forces the indices to range over a finite set. A constant subsequence argument then
-- shows the weak limit still belongs to the set.
/-- The range of a weighted orthonormal sequence with weights tending to `+∞` is weakly
sequentially closed. -/
private theorem isSeqClosed_scaled_orthonormal_range_in_weakSpace (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_tendsto : Tendsto α atTop atTop) :
    IsSeqClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) := by
  intro u x hu hx
  classical
  have hu_exists : ∀ k, ∃ m : ℕ, u k = toWeakSpace ℝ 𝓗 (α m • e m) := by
    intro k
    rcases hu k with ⟨y, hy, hyu⟩
    rcases Set.mem_range.1 hy with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    calc
      u k = toWeakSpace ℝ 𝓗 y := hyu.symm
      _ = toWeakSpace ℝ 𝓗 (α m • e m) := by simp [hm]
  choose n hn using hu_exists
  have hseq_tendsto :
      Tendsto (fun k ↦ toWeakSpace ℝ 𝓗 (α (n k) • e (n k))) atTop (𝓝 x) := by
    exact hx.congr' (Filter.Eventually.of_forall hn)
  -- Weak convergence bounds the range, and divergence of `α` then traps the indices in a finite set.
  have hbounded : Bornology.IsBounded (Set.range fun k ↦ α (n k) • e (n k)) := by
    simpa using bounded_range_of_tendsto_weakly hseq_tendsto
  rcases exists_constant_subseq_of_bounded_scaled_orthonormal_values e he α hα_tendsto hbounded
    with ⟨φ, hφ, j, hj⟩
  have hsub_tendsto :
      Tendsto (fun k ↦ toWeakSpace ℝ 𝓗 (α (n (φ k)) • e (n (φ k)))) atTop (𝓝 x) := by
    simpa [Function.comp] using hseq_tendsto.comp hφ.tendsto_atTop
  -- Along that subsequence the weak image is constant, so Hausdorffness identifies the limit.
  have hconst_tendsto :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ 𝓗 (α j • e j)) atTop (𝓝 x) := by
    convert hsub_tendsto using 1
    ext k
    simp [hj k]
  have hx_eq : x = toWeakSpace ℝ 𝓗 (α j • e j) :=
    tendsto_nhds_unique hconst_tendsto tendsto_const_nhds
  exact ⟨α j • e j, Set.mem_range.2 ⟨j, rfl⟩, hx_eq.symm⟩

-- Proof sketch: describe a basic weak neighborhood of `0` using finitely many inner-product
-- inequalities. Bessel's inequality makes the resulting coefficient sequence square summable, while
-- the assumption that `∑ (α n)⁻²` diverges guarantees infinitely many indices for which
-- `α n • e n` satisfies those inequalities, so every weak neighborhood of `0` meets the set.
omit [CompleteSpace 𝓗] in
/-- Helper for Example 3.33: every weak neighborhood of `0` contains a finite tube cut out by
continuous linear functionals. -/
private lemma weakspace_zero_nhds_contains_finite_dual_tube {V : Set (WeakSpace ℝ 𝓗)}
    (hV : V ∈ 𝓝 (0 : WeakSpace ℝ 𝓗)) :
    ∃ s : Finset (StrongDual ℝ 𝓗), ∃ ε > 0,
      {x : WeakSpace ℝ 𝓗 | ∀ f ∈ s, ‖f ((toWeakSpace ℝ 𝓗).symm x)‖ < ε} ⊆ V := by
  let B : 𝓗 →ₗ[ℝ] StrongDual ℝ 𝓗 →ₗ[ℝ] ℝ := (topDualPairing ℝ 𝓗).flip
  have hbasis := LinearMap.hasBasis_weakBilin B
  rcases hbasis.mem_iff.mp hV with ⟨U, hU, hUV⟩
  rcases (SeminormFamily.basisSets_iff _).mp hU with ⟨s, ε, hε, rfl⟩
  refine ⟨s, ε, hε, ?_⟩
  intro x hx
  -- Rewrite the basic seminorm ball as simultaneous smallness for finitely many evaluations.
  have hx' : x ∈ (s.sup (LinearMap.toSeminormFamily B)).ball 0 ε := by
    rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hε]
    apply Set.mem_biInter
    intro f hf
    change x ∈
      {y : WeakSpace ℝ 𝓗 |
        (((topDualPairing ℝ 𝓗).flip.toSeminormFamily f) (y - (0 : WeakSpace ℝ 𝓗)) < ε)}
    simp only [Set.mem_setOf_eq, sub_zero]
    rw [LinearMap.toSeminormFamily_apply]
    simpa [toWeakSpace] using hx f hf
  exact hUV hx'

/-- Helper for Example 3.33: for a finite family of continuous linear functionals, the sum of their
evaluation norms on an orthonormal sequence is square-summable. -/
private lemma summable_sq_finset_dual_eval_sum (s : Finset (StrongDual ℝ 𝓗)) (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) :
    Summable (fun n ↦ (∑ f ∈ s, ‖f (e n)‖) ^ 2) := by
  have hf_sq : ∀ f : StrongDual ℝ 𝓗, Summable (fun n ↦ ‖f (e n)‖ ^ 2) := by
    intro f
    let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
    have hrepr : (fun n ↦ ‖f (e n)‖ ^ 2) = fun n ↦ ‖inner ℝ (e n) u‖ ^ 2 := by
      -- The Riesz representer converts each functional into inner products with a fixed vector.
      ext n
      rw [← InnerProductSpace.toDual_symm_apply]
      rw [real_inner_comm]
    rw [hrepr]
    exact he.inner_products_summable u
  have hsum : Summable (fun n ↦ ∑ f ∈ s, ‖f (e n)‖ ^ 2) := by
    classical
    -- Summability survives finite addition once each coordinate sequence is summable.
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha ih =>
        simpa [Finset.sum_insert, ha] using (hf_sq a).add ih
  have hmajor : Summable (fun n ↦ (s.card : ℝ) * ∑ f ∈ s, ‖f (e n)‖ ^ 2) := by
    simpa [mul_comm] using hsum.mul_left (s.card : ℝ)
  -- Chebyshev's inequality controls the square of the sum by the sum of the squares.
  refine hmajor.of_nonneg_of_le (fun n ↦ sq_nonneg _) ?_
  intro n
  have hsq_sum :
      (∑ f ∈ s, ‖f (e n)‖) ^ 2 ≤ (s.card : ℝ) * ∑ f ∈ s, ‖f (e n)‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq :
        (∑ f ∈ s, ‖f (e n)‖) ^ 2 ≤ (s.card : ℝ) * ∑ f ∈ s, ‖f (e n)‖ ^ 2)
  simpa using hsq_sum

/-- Helper for Example 3.33: some weighted orthonormal vector is simultaneously small on any
finite family of continuous linear functionals. -/
private lemma exists_weighted_orthonormal_vector_small_on_finite_functionals (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n)
    (hα_invSq_not_summable : ¬ Summable (fun n ↦ ((α n)⁻¹)^2))
    (s : Finset (StrongDual ℝ 𝓗)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ f ∈ s, ‖f (α n • e n)‖ < ε := by
  let zeta : ℕ → ℝ := fun n ↦ ∑ f ∈ s, ‖f (e n)‖
  have hzeta_sq : Summable (fun n ↦ (zeta n)^2) := by
    -- This is the Bessel part of the source proof for the chosen finite family.
    simpa [zeta] using summable_sq_finset_dual_eval_sum s e he
  by_contra hnone
  have hbad : ∀ n : ℕ, ∃ f ∈ s, ε ≤ ‖f (α n • e n)‖ := by
    intro n
    by_contra hNo
    apply hnone
    refine ⟨n, ?_⟩
    intro f hf
    by_contra hge
    exact hNo ⟨f, hf, le_of_not_gt hge⟩
  have hdom : ∀ n : ℕ, ε^2 * ((α n)⁻¹)^2 ≤ (zeta n)^2 := by
    intro n
    rcases hbad n with ⟨f, hf, hfε⟩
    have hα_nonneg : 0 ≤ α n := le_trans zero_le_one (hα_ge_one n)
    have hα_pos : 0 < α n := lt_of_lt_of_le zero_lt_one (hα_ge_one n)
    have hzeta_nonneg : 0 ≤ zeta n := by
      exact Finset.sum_nonneg (fun g hg ↦ norm_nonneg _)
    have hscale : ‖f (α n • e n)‖ = α n * ‖f (e n)‖ := by
      -- Positivity of `α n` removes the absolute value from the scalar factor.
      rw [map_smul, norm_smul, Real.norm_of_nonneg hα_nonneg]
    have hterm_le : ‖f (e n)‖ ≤ zeta n := by
      let w : StrongDual ℝ 𝓗 → ℝ := fun g ↦ ‖g (e n)‖
      -- The offending coordinate is one summand of `zeta n`.
      have hw_nonneg : ∀ g ∈ s, 0 ≤ w g := fun g hg ↦ norm_nonneg _
      simpa [zeta, w] using (Finset.single_le_sum hw_nonneg hf)
    have hε_le : ε ≤ α n * zeta n := by
      calc
        ε ≤ ‖f (α n • e n)‖ := hfε
        _ = α n * ‖f (e n)‖ := hscale
        _ ≤ α n * zeta n := by gcongr
    have hdiv : ε * (α n)⁻¹ ≤ zeta n := by
      -- Divide the lower bound by the positive weight `α n`.
      rw [mul_inv_le_iff₀ hα_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hε_le
    have hsq : (ε * (α n)⁻¹)^2 ≤ (zeta n)^2 := by
      gcongr
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hsummable_inv_scaled : Summable (fun n ↦ ε^2 * ((α n)⁻¹)^2) := by
    -- Domination by the square-summable sequence `zeta n ^ 2` forces summability.
    refine hzeta_sq.of_nonneg_of_le (fun n ↦ by positivity) hdom
  have hε2_ne : ε^2 ≠ 0 := by
    positivity
  have hsummable_inv : Summable (fun n ↦ ((α n)⁻¹)^2) := by
    exact (summable_mul_left_iff hε2_ne).1 hsummable_inv_scaled
  exact hα_invSq_not_summable hsummable_inv

/-- The origin belongs to the weak closure of the range when the inverse-square weights are not
summable. -/
private theorem zero_mem_closure_scaled_orthonormal_range_in_weakSpace (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n)
    (hα_invSq_not_summable : ¬ Summable (fun n ↦ ((α n)⁻¹)^2)) :
    (0 : WeakSpace ℝ 𝓗) ∈ closure ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) := by
  -- Route correction: instead of converting neighborhoods to inner-product coordinates first,
  -- extract the canonical finite family of dual functionals from the weak-topology basis.
  rw [mem_closure_iff_nhds]
  intro V hV
  rcases weakspace_zero_nhds_contains_finite_dual_tube hV with ⟨s, ε, hε, hsubset⟩
  rcases exists_weighted_orthonormal_vector_small_on_finite_functionals e he α hα_ge_one
      hα_invSq_not_summable s hε with ⟨n, hn⟩
  -- The selected weighted orthonormal vector lies in the extracted tube, hence in `V`.
  have hsmall :
      toWeakSpace ℝ 𝓗 (α n • e n) ∈
        {x : WeakSpace ℝ 𝓗 | ∀ f ∈ s, ‖f ((toWeakSpace ℝ 𝓗).symm x)‖ < ε} := by
    show ∀ f ∈ s, ‖f ((toWeakSpace ℝ 𝓗).symm (toWeakSpace ℝ 𝓗 (α n • e n)))‖ < ε
    simpa [toWeakSpace] using hn
  refine ⟨toWeakSpace ℝ 𝓗 (α n • e n), ?_⟩
  constructor
  · exact hsubset hsmall
  · exact ⟨α n • e n, Set.mem_range.2 ⟨n, rfl⟩, rfl⟩

-- Proof sketch: if `0 = α n • e n`, taking norms gives `0 = α n * ‖e n‖ = α n`, but
-- orthonormality gives `‖e n‖ = 1` and `hα_ge_one` yields `α n ≥ 1`, a contradiction.
omit [CompleteSpace 𝓗] in
/-- The origin does not belong to the range of a weighted orthonormal sequence whose weights are at
least `1`. -/
private theorem zero_not_mem_scaled_orthonormal_range (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) :
    (0 : 𝓗) ∉ Set.range (fun n ↦ α n • e n) := by
  rintro hx
  rcases Set.mem_range.1 hx with ⟨n, hn⟩
  have hα_nonneg : 0 ≤ α n := le_trans zero_le_one (hα_ge_one n)
  -- Taking norms turns the equation `0 = α n • e n` into the contradiction `0 = α n ≥ 1`.
  have hnorm_eq : ‖α n • e n‖ = α n := by
    rw [norm_smul, he.norm_eq_one n, mul_one, Real.norm_of_nonneg hα_nonneg]
  have hα_zero : α n = 0 := by
    calc
      α n = ‖α n • e n‖ := hnorm_eq.symm
      _ = ‖(0 : 𝓗)‖ := by simp [hn]
      _ = 0 := norm_zero
  have hcontr : (1 : ℝ) ≤ 0 := by
    simpa [hα_zero] using hα_ge_one n
  linarith

-- Proof sketch: combine the weak sequential closedness statement with the fact that `0` lies in
-- the weak closure but not in the set itself; a weakly closed set would contain all points of its
-- weak closure.
/-- Example 3.33: for `C = {α n • e n | n : ℕ}` coming from an orthonormal sequence and a
monotone weight sequence in `[1, +∞)` tending to `+∞` with non-summable inverse squares, `C` is
norm closed and weakly sequentially closed, is not weakly closed, and satisfies
`0 ∈ closure ((toWeakSpace ℝ 𝓗) '' C)` and `0 ∉ C`. -/
theorem scaled_orthonormal_range_weaklySeqClosed_and_not_weaklyClosed (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n)
    (_hα_monotone : Monotone α) (hα_tendsto : Tendsto α atTop atTop)
    (hα_invSq_not_summable : ¬ Summable (fun n ↦ ((α n)⁻¹)^2)) :
    IsClosed (Set.range (fun n ↦ α n • e n)) ∧
      IsSeqClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) ∧
      ¬ IsClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) ∧
      (0 : WeakSpace ℝ 𝓗) ∈ closure ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) ∧
      (0 : 𝓗) ∉ Set.range (fun n ↦ α n • e n) := by
  have hseqClosed :
      IsSeqClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) :=
    isSeqClosed_scaled_orthonormal_range_in_weakSpace e he α hα_tendsto
  have hzero_mem_closure :
      (0 : WeakSpace ℝ 𝓗) ∈ closure ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) :=
    zero_mem_closure_scaled_orthonormal_range_in_weakSpace e he α hα_ge_one
      hα_invSq_not_summable
  have hzero_not_mem : (0 : 𝓗) ∉ Set.range (fun n ↦ α n • e n) :=
    zero_not_mem_scaled_orthonormal_range e he α hα_ge_one
  refine ⟨isClosed_scaled_orthonormal_range e he α hα_ge_one, hseqClosed, ?_, hzero_mem_closure,
    hzero_not_mem⟩
  intro hclosed
  have hzero_mem :
      (0 : WeakSpace ℝ 𝓗) ∈ ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) := by
    rw [← hclosed.closure_eq]
    exact hzero_mem_closure
  rcases hzero_mem with ⟨y, hy, hy0⟩
  have hy_zero : y = 0 := (toWeakSpace ℝ 𝓗).injective (by simpa using hy0)
  exact hzero_not_mem (hy_zero ▸ hy)
