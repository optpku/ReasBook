/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Corollary 3.36: weak convergence places the limit in the norm closure of the convex
hull of the sequence range. -/
private lemma mem_closure_convexHull_of_tendsto_weakly
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    x ∈ closure (convexHull ℝ (Set.range xₙ)) := by
  let s : Set E := convexHull ℝ (Set.range xₙ)
  have hs_convex : Convex ℝ s := by
    -- The weak/strong closure comparison applies to the convex hull itself.
    simpa [s] using convex_convexHull ℝ (Set.range xₙ)
  have hmem : ∀ n, (xₙ n : WeakSpace ℝ E) ∈ (toWeakSpace ℝ E) '' s := by
    intro n
    -- Each sequence term already lies in the convex hull through the singleton inclusion.
    refine ⟨xₙ n, ?_, rfl⟩
    exact subset_convexHull ℝ (Set.range xₙ) (show xₙ n ∈ Set.range xₙ from ⟨n, rfl⟩)
  have hxWeak : toWeakSpace ℝ E x ∈ closure ((toWeakSpace ℝ E) '' s) := by
    -- Closedness of the weak closure gives the limit point in the weak closure.
    exact mem_closure_of_tendsto hx (Filter.Eventually.of_forall hmem)
  rw [← hs_convex.toWeakSpace_closure (𝕜 := ℝ)] at hxWeak
  rcases hxWeak with ⟨y, hy, hyx⟩
  have hxy : y = x := (toWeakSpace ℝ E).injective hyx
  simpa [hxy] using hy

section

variable {X : Type u}

/-- Helper for Corollary 3.36: a finite subset of the sequence range is already contained in some
finite initial segment. -/
private lemma finite_subset_range_subset_initialSegment
    (xₙ : ℕ → X) (s : Finset X)
    (hs : (↑s : Set X) ⊆ Set.range xₙ) :
    ∃ N : ℕ, (↑s : Set X) ⊆ Set.range (fun k : Fin (N + 1) ↦ xₙ k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro y hy
      simp at hy
  | @insert a s ha ih =>
      have ha_range : a ∈ Set.range xₙ := hs (by simp)
      rcases ha_range with ⟨na, rfl⟩
      have hs_tail : ((↑s : Set X) ⊆ Set.range xₙ) := by
        -- Remove the head point and recurse on the remaining finite subset.
        intro y hy
        exact hs (by simp [hy])
      rcases ih hs_tail with ⟨N, hN⟩
      refine ⟨max na N, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · -- The newly inserted point is represented by its original sequence index.
        refine ⟨⟨na, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩, rfl⟩
      · -- Points from the tail keep their witnesses after enlarging the initial segment.
        rcases hN hy with ⟨k, hk⟩
        refine ⟨⟨k.1, Nat.lt_succ_of_le ?_⟩, hk⟩
        exact Nat.le_trans (Nat.le_of_lt_succ k.2) (Nat.le_max_right _ _)

end

/-- Helper for Corollary 3.36: every norm-neighborhood of the weak limit meets some finite
initial-segment convex hull. -/
private lemma exists_point_initialSegment_convexHull_dist_lt
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N z,
      z ∈ convexHull ℝ (Set.range fun k : Fin (N + 1) ↦ xₙ k) ∧
      dist x z < ε := by
  have hxmem : x ∈ closure (convexHull ℝ (Set.range xₙ)) :=
    mem_closure_convexHull_of_tendsto_weakly xₙ x hx
  rcases Metric.mem_closure_iff.mp hxmem ε hε with ⟨z, hz, hdist⟩
  rw [convexHull_eq_union_convexHull_finite_subsets] at hz
  rcases Set.mem_iUnion.mp hz with ⟨s, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hs, hzs⟩
  rcases finite_subset_range_subset_initialSegment xₙ s hs with ⟨N, hN⟩
  refine ⟨N, z, convexHull_mono hN hzs, hdist⟩

/-- Helper for Corollary 3.36: the distances from `x` to the convex hulls of the initial segments
of the sequence tend to `0`. -/
private lemma tendsto_infDist_initialSegment_convexHull
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    Tendsto
      (fun n ↦ Metric.infDist x (convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)))
      atTop (𝓝 0) := by
  let C : ℕ → Set E := fun n ↦ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)
  have hC_mono : ∀ {m n : ℕ}, m ≤ n → C m ⊆ C n := by
    intro m n hmn
    -- Enlarging the initial segment enlarges its convex hull.
    refine convexHull_mono ?_
    intro y hy
    rcases hy with ⟨k, rfl⟩
    refine ⟨⟨k.1, Nat.lt_of_lt_of_le k.2 (Nat.succ_le_succ hmn)⟩, rfl⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    -- Distances are always nonnegative, so lower neighborhoods of `0` are automatic.
    exact Filter.Eventually.of_forall fun n ↦ lt_of_lt_of_le ha Metric.infDist_nonneg
  · intro ε hε
    rcases exists_point_initialSegment_convexHull_dist_lt xₙ x hx hε with ⟨N, z, hzC, hdist⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hzCn : z ∈ C n := hC_mono hn hzC
    exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hzCn) hdist

-- Proof sketch: let `C := convexHull ℝ (Set.range xₙ)`. Weak convergence of `xₙ` to `x` implies
-- that `x` belongs to the weak closure of `C`; apply the preceding closed-convex weak/strong
-- closure equivalence to identify this with the norm closure of `C`. Then approximate `x` in norm
-- by points of `C`, pass to convex combinations supported on finitely many initial segments, and
-- choose for each `n` a convex combination of `xₙ 0, …, xₙ n` whose distance to `x` is within
-- `1 / (n + 1)` of the infimum over that finite convex hull.
/-- Corollary 3.36: (Mazur's lemma) if a sequence in a real normed space converges weakly to
`x`, then one can choose a sequence of convex combinations of the initial segments
`xₙ 0, …, xₙ n` that converges strongly to `x`. -/
theorem exists_stronglyConvergent_convex_combinations_of_tendsto_weakly
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    ∃ y : ℕ → E,
      (∀ n, y n ∈ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)) ∧
      Tendsto y atTop (𝓝 x) := by
  classical
  let C : ℕ → Set E := fun n ↦ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)
  have hC_nonempty : ∀ n, (C n).Nonempty := by
    intro n
    refine ⟨xₙ 0, ?_⟩
    -- Each initial-segment convex hull contains its first point.
    exact subset_convexHull ℝ _ ⟨0, rfl⟩
  have hd :
      Tendsto (fun n ↦ Metric.infDist x (C n)) atTop (𝓝 0) :=
    tendsto_infDist_initialSegment_convexHull xₙ x hx
  have hy_exists :
      ∀ n, ∃ z ∈ C n, dist x z < Metric.infDist x (C n) + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt :
        Metric.infDist x (C n) <
          Metric.infDist x (C n) + 1 / ((n : ℝ) + 1) := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    -- Pick an almost-minimizer for the distance to the `n`th finite convex hull.
    exact (Metric.infDist_lt_iff (hC_nonempty n)).mp hlt
  choose y hy_mem hy_dist using hy_exists
  refine ⟨y, hy_mem, ?_⟩
  have hy_dist_le :
      ∀ n, dist (y n) x ≤ Metric.infDist x (C n) + 1 / ((n : ℝ) + 1) := by
    intro n
    simpa [dist_comm] using le_of_lt (hy_dist n)
  have hbound :
      Tendsto
        (fun n ↦ Metric.infDist x (C n) + 1 / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    -- The quantitative error is the sum of the hull-distance and the auxiliary `1 / (n + 1)`.
    simpa using hd.add (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
      (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hdist :
      Tendsto (fun n ↦ dist (y n) x) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ dist_nonneg) hy_dist_le hbound
  -- Strong convergence is exactly convergence of the distances to `x`.
  exact tendsto_iff_dist_tendsto_zero.2 hdist

/-- Helper for Corollary 3.36: membership in an initial-segment convex hull yields explicit convex
coefficients on that initial segment. -/
private lemma exists_coefficients_of_mem_initialSegment_convexHull
    (xₙ : ℕ → E) {n : ℕ} {y : E}
    (hy : y ∈ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)) :
    ∃ α : Fin (n + 1) → ℝ,
      (∀ k, α k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∑ k, α k = 1) ∧
      (y = ∑ k, α k • xₙ k) := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hy
  rcases hy with ⟨s, w, hw₀, hw₁, rfl⟩
  let α : Fin (n + 1) → ℝ := fun k ↦ if k ∈ s then w k else 0
  have hy_linear :
      s.affineCombination ℝ (fun k : Fin (n + 1) ↦ xₙ k) w =
        Finset.sum s (fun k : Fin (n + 1) ↦ w k • xₙ k) := by
    -- In a vector space, affine combinations are just linear combinations when the weights sum to
    -- `1`.
    simpa using
      (Finset.affineCombination_eq_linear_combination s
        (fun k : Fin (n + 1) ↦ xₙ k) w hw₁)
  have hy_univ :
      Finset.sum s (fun k : Fin (n + 1) ↦ w k • xₙ k) =
        Finset.univ.sum (fun k : Fin (n + 1) ↦ α k • xₙ k) := by
    -- Extending the finite support by zero does not change the resulting sum.
    calc
      Finset.sum s (fun k : Fin (n + 1) ↦ w k • xₙ k) =
          Finset.univ.sum (fun k : Fin (n + 1) ↦ if k ∈ s then w k • xₙ k else 0) := by
        symm
        exact Finset.sum_ite_mem_eq s (fun k : Fin (n + 1) ↦ w k • xₙ k)
      _ = Finset.univ.sum (fun k : Fin (n + 1) ↦ α k • xₙ k) := by
        simp [α]
  have hαsum : Finset.univ.sum α = 1 := by
    -- The zero extension preserves the total mass of the coefficients.
    simpa [α] using (Finset.sum_ite_mem_eq s w).trans hw₁
  refine ⟨α, ?_, ?_, ?_⟩
  · intro k
    constructor
    · by_cases hk : k ∈ s
      · simpa [α, hk] using hw₀ k hk
      · simp [α, hk]
    · by_cases hk : k ∈ s
      · have hk_le : w k ≤ ∑ j ∈ s, w j := by
          -- A nonnegative coefficient is bounded above by the total sum of all coefficients.
          simpa [Finset.sum_erase_add _ _ hk] using
            (Finset.single_le_sum (fun j hj ↦ hw₀ j hj) hk : w k ≤ ∑ j ∈ s, w j)
        simpa [hw₁, α, hk] using hk_le
      · simp [α, hk]
  · simp [hαsum]
  · simp [hy_linear.trans hy_univ]

/-- A coefficient-form companion to Mazur's lemma: the approximating sequence may be written using
explicit convex-combination coefficients on each initial segment. -/
-- Proof sketch: apply the convex-hull formulation above to obtain `y n ∈ convexHull ℝ
-- (Set.range fun k : Fin (n + 1) ↦ xₙ k)` for every `n`, then use the finite-dimensional
-- characterization of membership in a convex hull of a finite set to choose coefficients
-- `α n k ∈ [0, 1]` summing to `1` with `y n = ∑ k, α n k • xₙ k`.
theorem exists_stronglyConvergent_initialSegment_coefficients_of_tendsto_weakly
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    ∃ α : (n : ℕ) → Fin (n + 1) → ℝ,
      (∀ n k, α n k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ∑ k, α n k = 1) ∧
      Tendsto (fun n ↦ ∑ k, α n k • xₙ k) atTop (𝓝 x) := by
  rcases exists_stronglyConvergent_convex_combinations_of_tendsto_weakly xₙ x hx with
    ⟨y, hy_mem, hy_tendsto⟩
  have hα :
      ∀ n, ∃ α : Fin (n + 1) → ℝ,
        (∀ k, α k ∈ Set.Icc (0 : ℝ) 1) ∧
        (∑ k, α k = 1) ∧
        (y n = ∑ k, α k • xₙ k) := by
    intro n
    -- Convert each convex-hull membership statement into explicit coefficients.
    exact exists_coefficients_of_mem_initialSegment_convexHull xₙ (hy_mem n)
  choose α hα_mem hα_sum hα_eq using hα
  have hy_def : y = fun n ↦ ∑ k, α n k • xₙ k := by
    funext n
    exact hα_eq n
  exact ⟨α, hα_mem, hα_sum, hy_def ▸ hy_tendsto⟩
