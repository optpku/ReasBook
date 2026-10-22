/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

private noncomputable def projectionSequence
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) : ℕ → 𝓗 :=
  fun n ↦
    projectionPoint (C n)
      (isChebyshev_of_nonempty_isClosed_convex (h_nonempty n) (h_closed n) (h_convex n)) 0

private noncomputable def projectionEnergy
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) : ℕ → ℝ :=
  fun n ↦ ‖projectionSequence C h_nonempty h_closed h_convex n‖ ^ 2

/-- A projection onto a later set lies in every earlier set of an antitone family. -/
private lemma projection_mem_of_le
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) {m n : ℕ} (hmn : m ≤ n) :
    projectionSequence C h_nonempty h_closed h_convex n ∈ C m := by
  -- Then the canonical projection point onto `C n` belongs to every earlier set `C m`.
  exact h_anti hmn <|
    projectionPoint_mem (C n)
      (isChebyshev_of_nonempty_isClosed_convex (h_nonempty n) (h_closed n) (h_convex n)) 0

/-- The squared norms of the projection sequence are monotone. -/
private lemma projection_norm_sq_monotone
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) :
    Monotone (projectionEnergy C h_nonempty h_closed h_convex) := by
  intro m n hmn
  -- The later projection is an admissible competitor for the earlier projection problem.
  have hnorm :
      dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex m) ≤
        dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex n) := by
    calc
      dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex m) =
          Metric.infDist 0 (C m) := by
            simpa [projectionSequence] using
              (projectionPoint_isBestApproximation (C m)
                (isChebyshev_of_nonempty_isClosed_convex
                  (h_nonempty m) (h_closed m) (h_convex m)) 0).2
      _ ≤ dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex n) :=
        Metric.infDist_le_dist_of_mem <|
          projection_mem_of_le C h_nonempty h_closed h_convex h_anti hmn
  -- Squaring preserves the order because both norms are nonnegative.
  dsimp [projectionEnergy]
  have hnorm' : ‖projectionSequence C h_nonempty h_closed h_convex m‖ ≤
      ‖projectionSequence C h_nonempty h_closed h_convex n‖ := by
    simpa [projectionSequence, dist_eq_norm] using hnorm
  nlinarith [hnorm', norm_nonneg (projectionSequence C h_nonempty h_closed h_convex m),
    norm_nonneg (projectionSequence C h_nonempty h_closed h_convex n)]

/-- The projection gap is controlled by the increase in the energy. -/
private lemma projection_gap_sq_le_of_le
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) {m n : ℕ} (hmn : m ≤ n) :
    ‖projectionSequence C h_nonempty h_closed h_convex n -
        projectionSequence C h_nonempty h_closed h_convex m‖ ^ 2 ≤
      projectionEnergy C h_nonempty h_closed h_convex n -
        projectionEnergy C h_nonempty h_closed h_convex m := by
  let pm := projectionSequence C h_nonempty h_closed h_convex m
  let pn := projectionSequence C h_nonempty h_closed h_convex n
  have hpn_mem : pn ∈ C m := by
    -- Nestedness places the later projection point inside the earlier set.
    simpa [pn] using projection_mem_of_le C h_nonempty h_closed h_convex h_anti hmn
  have hproj :
      pm =
        projectionPoint (C m)
          (isChebyshev_of_nonempty_isClosed_convex (h_nonempty m) (h_closed m) (h_convex m)) 0 :=
    rfl
  have hinner_nonneg : 0 ≤ ⟪pn - pm, pm⟫_ℝ := by
    -- The variational inequality for the projection of `0` gives the sign of the cross term.
    have hchar :
        pm =
            projectionPoint (C m)
              (isChebyshev_of_nonempty_isClosed_convex
                (h_nonempty m) (h_closed m) (h_convex m)) 0 ↔
          pm ∈ C m ∧ ∀ y ∈ C m, ⟪y - pm, (0 : 𝓗) - pm⟫_ℝ ≤ 0 :=
      eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (h_nonempty m) (h_closed m) (h_convex m)
    have hineq : ⟪pn - pm, (0 : 𝓗) - pm⟫_ℝ ≤ 0 := (hchar.mp hproj).2 pn hpn_mem
    simpa using neg_nonneg.mpr hineq
  have hsq := norm_add_sq_real (pn - pm) pm
  have hrewrite : (pn - pm) + pm = pn := by
    simp [pn, pm]
  -- Expand `‖pn‖²` and discard the nonnegative cross term.
  rw [hrewrite] at hsq
  dsimp [projectionEnergy]
  nlinarith

/-- The projection sequence onto the nested sets is Cauchy. -/
private lemma projection_sequence_cauchy
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_bounded : ∀ n, Bornology.IsBounded (C n))
    (h_closed : ∀ n, IsClosed (C n)) (h_convex : ∀ n, Convex ℝ (C n))
    (h_anti : Antitone C) :
    CauchySeq (projectionSequence C h_nonempty h_closed h_convex) := by
  let p := projectionSequence C h_nonempty h_closed h_convex
  let s := projectionEnergy C h_nonempty h_closed h_convex
  have hs_mono : Monotone s := projection_norm_sq_monotone C h_nonempty h_closed h_convex h_anti
  obtain ⟨R, hR_pos, hR⟩ := (h_bounded 0).exists_pos_norm_le
  have hp_mem_zero : ∀ n, p n ∈ C 0 := by
    intro n
    -- Every projection lies in the first set because the family is decreasing.
    simpa [p] using projection_mem_of_le C h_nonempty h_closed h_convex h_anti (Nat.zero_le n)
  have hs_bdd : BddAbove (Set.range s) := by
    refine ⟨R ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    -- Boundedness of `C 0` bounds every term of the energy sequence.
    have hpn_norm : ‖p n‖ ≤ R := hR (p n) (hp_mem_zero n)
    dsimp [s, projectionEnergy]
    nlinarith [hR_pos, hpn_norm, norm_nonneg (p n)]
  let L : ℝ := ⨆ n, s n
  have hs_lim : Filter.Tendsto s Filter.atTop (nhds L) := by
    -- A monotone bounded real sequence converges to its supremum.
    simpa [L] using tendsto_atTop_ciSup hs_mono hs_bdd
  have hsqrt_lim : Filter.Tendsto (fun N ↦ Real.sqrt (L - s N)) Filter.atTop (nhds 0) := by
    -- The tail energy above level `N` shrinks to zero, so its square root also tends to zero.
    have hsub_lim : Filter.Tendsto (fun N ↦ L - s N) Filter.atTop (nhds (L - L)) := by
      exact tendsto_const_nhds.sub hs_lim
    have hsqrt' :
        Filter.Tendsto (fun N ↦ Real.sqrt (L - s N)) Filter.atTop (nhds (Real.sqrt (L - L))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsub_lim
    simpa using hsqrt'
  refine cauchySeq_of_le_tendsto_0 (fun N ↦ Real.sqrt (L - s N)) ?_ hsqrt_lim
  intro n m N hNn hNm
  by_cases hnm : n ≤ m
  · have hgap :
        ‖p m - p n‖ ^ 2 ≤ s m - s n := by
      simpa [p, s, norm_sub_rev] using
        projection_gap_sq_le_of_le C h_nonempty h_closed h_convex h_anti hnm
    have htail_nonneg : 0 ≤ L - s N := sub_nonneg.mpr (le_ciSup hs_bdd N)
    have htail_sq : ‖p m - p n‖ ^ 2 ≤ L - s N := by
      have hsNn : s N ≤ s n := hs_mono hNn
      have hsmL : s m ≤ L := le_ciSup hs_bdd m
      linarith
    -- Compare the norm with the square root of the tail energy.
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [htail_sq, Real.sq_sqrt htail_nonneg, norm_nonneg (p m - p n),
      Real.sqrt_nonneg (L - s N)]
  · have hmn : m ≤ n := le_of_not_ge hnm
    have hgap :
        ‖p n - p m‖ ^ 2 ≤ s n - s m := by
      simpa [p, s] using
        projection_gap_sq_le_of_le C h_nonempty h_closed h_convex h_anti hmn
    have htail_nonneg : 0 ≤ L - s N := sub_nonneg.mpr (le_ciSup hs_bdd N)
    have htail_sq : ‖p n - p m‖ ^ 2 ≤ L - s N := by
      have hsNm : s N ≤ s m := hs_mono hNm
      have hsnL : s n ≤ L := le_ciSup hs_bdd n
      linarith
    -- The symmetric estimate gives the same tail bound in the other index order.
    rw [dist_eq_norm]
    nlinarith [htail_sq, Real.sq_sqrt htail_nonneg, norm_nonneg (p n - p m),
      Real.sqrt_nonneg (L - s N)]

/-- Proposition 3.20: a decreasing sequence of nonempty bounded closed convex subsets of a real
Hilbert space has nonempty intersection. -/
theorem nonempty_iInter_of_nonempty_bounded_isClosed_convex
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_bounded : ∀ n, Bornology.IsBounded (C n))
    (h_closed : ∀ n, IsClosed (C n)) (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) :
    (⋂ n, C n).Nonempty := by
  let p := projectionSequence C h_nonempty h_closed h_convex
  have hp_cauchy : CauchySeq p :=
    projection_sequence_cauchy C h_nonempty h_bounded h_closed h_convex h_anti
  rcases cauchySeq_tendsto_of_complete hp_cauchy with ⟨q, hq_lim⟩
  refine ⟨q, ?_⟩
  simpa [Set.mem_iInter] using fun n ↦ by
    have htail_lim : Filter.Tendsto (fun k ↦ p (k + n)) Filter.atTop (nhds q) := by
    -- Shifting a convergent sequence preserves its limit.
      exact (Filter.tendsto_add_atTop_iff_nat n).2 hq_lim
    have htail_mem : ∀ k, p (k + n) ∈ C n := by
      intro k
      -- Every term of the shifted tail already lies in `C n`.
      simpa [p, Nat.add_comm] using projection_mem_of_le C h_nonempty h_closed h_convex h_anti
        (Nat.le_add_left n k)
    -- Closedness of each `C n` keeps the limit point inside that set.
    exact (h_closed n).mem_of_tendsto htail_lim (Filter.Eventually.of_forall htail_mem)
