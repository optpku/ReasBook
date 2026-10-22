/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped BigOperators Topology

variable {m n : ℕ}

/- Proposition New 2 lies in Chapter 7's sampled-prefix radius / subsequential compactness
domain.

Sampled owner-style declarations:
- `CentralSymmetryRoundingAlgorithm.selectedRadius` and the coercion to its inverse-matrix
  sequence in `Chap07/Algorithm_7_6`, the Chapter 7 owner of Algorithm 7.6's sampled radii and
  matrices;
- `bestRadiusUpTo` and `bestFunctionValueUpTo_le` in `Chap03/Definition_3_55`, the existing
  chapter owner
  for the sampled prefix minimum `min_{0 ≤ k ≤ N} r_k`;
- `summable_of_sum_range_le` in mathlib, the canonical bridge from uniformly bounded
  nonnegative partial sums to summability of the squared-gap sequence;
- `IsCompact.tendsto_subseq` and `MapClusterPt.tendsto_subseq` in mathlib, the canonical
  compactness and cluster-point bridges to convergent subsequences.

Best owner abstraction:
- source-facing: Proposition New 2's rate, convergence, and compactness conclusions for the
  selected radii and inverse matrices attached to Algorithm 7.6;
- core/canonical: `CentralSymmetryRoundingAlgorithm`, `bestRadiusUpTo`, and `MapClusterPt`;
- bridge/view: the direct subsequence and cluster-point data extracted from compactness.

Primitive data:
- the Algorithm 7.6 owner `algorithm`;
- the squared-deviation bound, the lower trace bound, compactness of `Set.range algorithm`, and
  the selected-radius sequence attached to that owner.

Derived API:
- the selected-radius sequence `algorithm.selectedRadius`;
- the sampled minimum `bestRadiusUpTo algorithm.selectedRadius N`;
- its lower bound from the trace hypothesis;
- the summable squared-gap sequence produced from the bounded partial sums;
- the direct subsequence and cluster-point data produced from compactness.

Source/core/bridge triage:
- source-facing: the three proposition statements below;
- core/canonical: `CentralSymmetryRoundingAlgorithm`, `bestRadiusUpTo`, the squared-gap
  sequence, and `MapClusterPt`;
- bridge/view: the explicit convergent subsequence and the selected-radius limit along it.

The previous version erased the Algorithm 7.6 owner and duplicated the chapter owner
`bestRadiusUpTo` under `partialMinRadius`. This refinement rewrites the file directly on
`CentralSymmetryRoundingAlgorithm.selectedRadius` and `bestRadiusUpTo`, keeping explicit
subsequence data only as the source-facing bridge.
-/

/-- Proposition New 2: if the selected radii `r_k = algorithm.selectedRadius k` attached to
Algorithm 7.6 satisfy the summation bound
`∑_{k=0}^N (1 - √n / r_k)^2 ≤ 2 n log R`
and the trace lower bound `√n ≤ r_k`, then the sampled minimum
`r_N^* = bestRadiusUpTo algorithm.selectedRadius N`
satisfies
`√n / r_N^* ≥ 1 - √(((2 n) / (N + 1)) log R)`. -/
-- Proof sketch: compare each squared gap in the prefix to the common squared gap built from
-- `bestRadiusUpTo algorithm.selectedRadius N`, average that pointwise inequality over the full
-- prefix, and then take square roots before rearranging the final linear bound.
theorem sqrt_div_bestRadiusUpTo_selectedRadius_ge_one_sub_sqrt_log_bound
    (algorithm : CentralSymmetryRoundingAlgorithm m n)
    {R : ℝ}
    (htrace_bound : ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ algorithm.selectedRadius k)
    (hsum :
      ∀ N : ℕ,
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) ≤
          2 * (n : ℝ) * Real.log R)
    (N : ℕ) :
    Real.sqrt (n : ℝ) / bestRadiusUpTo algorithm.selectedRadius N ≥
      1 - Real.sqrt (((2 * (n : ℝ)) / (N + 1 : ℝ)) * Real.log R) := by
  by_cases hn : n = 0
  · -- When `n = 0`, the `N = 0` summation hypothesis already gives a contradiction.
    have hfalse : False := by
      have hzero := hsum 0
      simp [hn] at hzero
      linarith
    exact False.elim hfalse
  · let c : ℝ := Real.sqrt (n : ℝ)
    let b : ℝ := bestRadiusUpTo algorithm.selectedRadius N
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hc_pos : 0 < c := by
      simpa [c] using Real.sqrt_pos.2 (show (0 : ℝ) < n by exact_mod_cast hn_pos)
    have hc_le_b : c ≤ b := by
      -- The prefix minimum stays above the common trace lower bound.
      dsimp [b, c, bestRadiusUpTo, bestFunctionValueUpTo]
      exact le_ciInf fun j ↦ htrace_bound j
    have hb_pos : 0 < b := lt_of_lt_of_le hc_pos hc_le_b
    have hpointwise :
        ∀ k < N + 1,
          (1 - c / b) ^ (2 : ℕ) ≤
            (1 - c / algorithm.selectedRadius k) ^ (2 : ℕ) := by
      intro k hk
      have hb_le_rk : b ≤ algorithm.selectedRadius k := by
        simpa [b, bestRadiusUpTo] using
          (bestFunctionValueUpTo_le
            (values := algorithm.selectedRadius) (k := N) ⟨k, hk⟩)
      have hc_le_rk : c ≤ algorithm.selectedRadius k := by
        simpa [c] using htrace_bound k
      have hrk_pos : 0 < algorithm.selectedRadius k := lt_of_lt_of_le hc_pos hc_le_rk
      have hratio_le : c / algorithm.selectedRadius k ≤ c / b := by
        exact div_le_div_of_nonneg_left hc_pos.le hb_pos hb_le_rk
      have hleft_nonneg : 0 ≤ 1 - c / b := by
        have hdiv_le_one : c / b ≤ 1 := by
          exact (div_le_one hb_pos).2 hc_le_b
        linarith
      have hright_nonneg : 0 ≤ 1 - c / algorithm.selectedRadius k := by
        have hdiv_le_one : c / algorithm.selectedRadius k ≤ 1 := by
          exact (div_le_one hrk_pos).2 hc_le_rk
        linarith
      have hgap_le : 1 - c / b ≤ 1 - c / algorithm.selectedRadius k := by
        linarith
      nlinarith
    have hsum_lower :
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (1 - c / b) ^ (2 : ℕ)) ≤
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - c / algorithm.selectedRadius k) ^ (2 : ℕ)) := by
      -- The common lower-bound term is dominated by every summand in the prefix.
      refine Finset.sum_le_sum ?_
      intro k hk
      exact hpointwise k (Finset.mem_range.mp hk)
    have hbound :
        (N + 1 : ℝ) * (1 - c / b) ^ (2 : ℕ) ≤ 2 * (n : ℝ) * Real.log R := by
      -- Average the pointwise estimate and reuse the assumed partial-sum bound.
      calc
        (N + 1 : ℝ) * (1 - c / b) ^ (2 : ℕ)
            = Finset.sum (Finset.range (N + 1)) (fun _ ↦ (1 - c / b) ^ (2 : ℕ)) := by
              simp
        _ ≤ Finset.sum (Finset.range (N + 1))
              (fun k ↦ (1 - c / algorithm.selectedRadius k) ^ (2 : ℕ)) :=
          hsum_lower
        _ ≤ 2 * (n : ℝ) * Real.log R :=
          hsum N
    have hN_pos : (0 : ℝ) < N + 1 := by
      exact_mod_cast Nat.succ_pos N
    have hsq_bound' :
        (1 - c / b) ^ (2 : ℕ) ≤ (2 * (n : ℝ) * Real.log R) / (N + 1 : ℝ) := by
      have hmul :=
        mul_le_mul_of_nonneg_right hbound (show 0 ≤ ((N + 1 : ℝ)⁻¹) by positivity)
      simpa [div_eq_mul_inv, hN_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hsq_bound :
        (1 - c / b) ^ (2 : ℕ) ≤ ((2 * (n : ℝ)) / (N + 1 : ℝ)) * Real.log R := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsq_bound'
    have hrhs_nonneg :
        0 ≤ ((2 * (n : ℝ)) / (N + 1 : ℝ)) * Real.log R := by
      exact le_trans (sq_nonneg (1 - c / b)) hsq_bound
    have hleft_nonneg : 0 ≤ 1 - c / b := by
      have hdiv_le_one : c / b ≤ 1 := by
        exact (div_le_one hb_pos).2 hc_le_b
      linarith
    have hroot_bound :
        1 - c / b ≤ Real.sqrt (((2 * (n : ℝ)) / (N + 1 : ℝ)) * Real.log R) := by
      -- Taking square roots converts the averaged square bound into the desired linear bound.
      have hsqrt_nonneg :
          0 ≤ Real.sqrt (((2 * (n : ℝ)) / (N + 1 : ℝ)) * Real.log R) := by
        exact Real.sqrt_nonneg _
      nlinarith [hsq_bound, hleft_nonneg, hsqrt_nonneg, Real.sq_sqrt hrhs_nonneg]
    -- Rearranging the linear bound gives the displayed rate estimate.
    linarith

/-- Helper for Proposition New 2: the selected radii converge to `√n` once the squared gaps
`(1 - √n / r_k)^2` have uniformly bounded partial sums. -/
private lemma selectedRadius_tendsto_sqrt_of_sq_gap_bound
    (algorithm : CentralSymmetryRoundingAlgorithm m n)
    {R : ℝ}
    (htrace_bound : ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ algorithm.selectedRadius k)
    (hsum :
      ∀ N : ℕ,
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) ≤
          2 * (n : ℝ) * Real.log R) :
    Tendsto algorithm.selectedRadius atTop (𝓝 (Real.sqrt (n : ℝ))) := by
  by_cases hn : n = 0
  · -- The `n = 0` case is inconsistent for the same reason as in the rate theorem.
    have hfalse : False := by
      have hzero := hsum 0
      simp [hn] at hzero
      linarith
    exact False.elim hfalse
  · let c : ℝ := Real.sqrt (n : ℝ)
    let a : ℕ → ℝ := fun k ↦ (1 - c / algorithm.selectedRadius k) ^ (2 : ℕ)
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hc_pos : 0 < c := by
      simpa [c] using Real.sqrt_pos.2 (show (0 : ℝ) < n by exact_mod_cast hn_pos)
    have hselected_pos : ∀ k : ℕ, 0 < algorithm.selectedRadius k := by
      intro k
      have hc_le_rk : c ≤ algorithm.selectedRadius k := by
        simpa [c] using htrace_bound k
      exact lt_of_lt_of_le hc_pos hc_le_rk
    have ha_nonneg : ∀ k : ℕ, 0 ≤ a k := by
      intro k
      positivity
    have hsum_range_le :
        ∀ N : ℕ, Finset.sum (Finset.range N) a ≤ 2 * (n : ℝ) * Real.log R := by
      intro N
      cases N with
      | zero =>
          have hzero_rhs : 0 ≤ 2 * (n : ℝ) * Real.log R := by
            have hzero := hsum 0
            have hleft_nonneg :
                0 ≤
                  Finset.sum (Finset.range (0 + 1))
                    (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) := by
              positivity
            exact le_trans hleft_nonneg hzero
          simpa using hzero_rhs
      | succ N =>
          simpa [a, c] using hsum N
    have hsummable_a : Summable a :=
      summable_of_sum_range_le ha_nonneg hsum_range_le
    have ha_tendsto_zero : Tendsto a atTop (𝓝 0) :=
      hsummable_a.tendsto_atTop_zero
    have hgap_tendsto_zero :
        Tendsto (fun k ↦ 1 - c / algorithm.selectedRadius k) atTop (𝓝 0) := by
      -- The gaps are nonnegative, so the square root of `a k` is exactly the unsquared gap.
      have hsqrt_tendsto :
          Tendsto (fun k ↦ Real.sqrt (a k)) atTop (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp ha_tendsto_zero
      have hgap_eq :
          (fun k ↦ Real.sqrt (a k)) = (fun k ↦ 1 - c / algorithm.selectedRadius k) := by
        funext k
        have hc_le_rk : c ≤ algorithm.selectedRadius k := by
          simpa [c] using htrace_bound k
        have hgap_nonneg : 0 ≤ 1 - c / algorithm.selectedRadius k := by
          have hdiv_le_one : c / algorithm.selectedRadius k ≤ 1 := by
            exact (div_le_one (hselected_pos k)).2 hc_le_rk
          linarith
        simp [a, Real.sqrt_sq_eq_abs, abs_of_nonneg hgap_nonneg]
      simpa [hgap_eq] using hsqrt_tendsto
    -- Recover the radii by applying continuity to `x ↦ c / (1 - x)` at `0`.
    have hradius_aux :
        Tendsto
          (fun k ↦ c / (1 - (1 - c / algorithm.selectedRadius k)))
          atTop
          (𝓝 (c / (1 - 0))) := by
      have hcont : ContinuousAt (fun x : ℝ ↦ c / (1 - x)) 0 := by
        exact
          continuousAt_const.div
            (continuousAt_const.sub continuousAt_id)
            (by norm_num)
      exact hcont.tendsto.comp hgap_tendsto_zero
    have hradius_eq :
        ∀ k : ℕ, c / (1 - (1 - c / algorithm.selectedRadius k)) = algorithm.selectedRadius k := by
      intro k
      have hdenom_eq :
          1 - (1 - c / algorithm.selectedRadius k) = c / algorithm.selectedRadius k := by
        ring
      rw [hdenom_eq]
      field_simp [hc_pos.ne', (hselected_pos k).ne']
    have hradius_tendsto :
        Tendsto algorithm.selectedRadius atTop (𝓝 (c / (1 - 0))) := by
      refine hradius_aux.congr' ?_
      exact Filter.Eventually.of_forall hradius_eq
    simpa [c] using hradius_tendsto

/-- Under the same summation and trace lower bounds, the sampled minima
`r_N^* = bestRadiusUpTo algorithm.selectedRadius N` converge to `√n`. -/
-- Proof sketch: first prove `algorithm.selectedRadius k → √n` from summability of the squared-gap
-- sequence, then squeeze the sampled prefix minima between the constant lower bound `√n` and the
-- current selected radius.
theorem tendsto_bestRadiusUpTo_selectedRadius
    (algorithm : CentralSymmetryRoundingAlgorithm m n)
    {R : ℝ}
    (htrace_bound : ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ algorithm.selectedRadius k)
    (hsum :
      ∀ N : ℕ,
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) ≤
          2 * (n : ℝ) * Real.log R) :
    Tendsto
      (fun N : ℕ ↦ bestRadiusUpTo algorithm.selectedRadius N)
      atTop
      (𝓝 (Real.sqrt (n : ℝ))) := by
  have hselected_tendsto :
      Tendsto algorithm.selectedRadius atTop (𝓝 (Real.sqrt (n : ℝ))) :=
    selectedRadius_tendsto_sqrt_of_sq_gap_bound
      (algorithm := algorithm) htrace_bound hsum
  -- Squeeze each sampled prefix minimum between the constant lower bound `√n` and the current
  -- selected radius.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hselected_tendsto ?_ ?_
  · intro N
    dsimp [bestRadiusUpTo, bestFunctionValueUpTo]
    exact le_ciInf fun j ↦ htrace_bound j
  · intro N
    simpa [bestRadiusUpTo] using
      (bestFunctionValueUpTo_le
        (values := algorithm.selectedRadius) (k := N) ⟨N, Nat.lt_succ_self N⟩)

/-- If the inverse matrices attached to Algorithm 7.6 form a compact set, then some subsequence
of inverse matrices converges, and along that same subsequence the selected radii converge to
`√n`. -/
-- Proof sketch: use `tendsto_bestRadiusUpTo_selectedRadius` to obtain
-- `bestRadiusUpTo algorithm.selectedRadius N → √n`, choose indices whose selected radii are
-- asymptotically close to those sampled minima, extract a convergent subsequence of the matrix
-- sequence from compactness of `Set.range algorithm`, and pass to the same subsequence on the
-- selected radii.
theorem exists_subseq_tendsto_selectedRadius_sqrt_of_compact_range
    (algorithm : CentralSymmetryRoundingAlgorithm m n)
    {R : ℝ}
    (htrace_bound : ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ algorithm.selectedRadius k)
    (hsum :
      ∀ N : ℕ,
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ (1 - Real.sqrt (n : ℝ) / algorithm.selectedRadius k) ^ (2 : ℕ)) ≤
          2 * (n : ℝ) * Real.log R)
    (hcompact : IsCompact (Set.range algorithm)) :
    ∃ Gstar : Matrix (Fin n) (Fin n) ℝ,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          Tendsto (algorithm ∘ φ) atTop (𝓝 Gstar) ∧
            Tendsto (algorithm.selectedRadius ∘ φ) atTop (𝓝 (Real.sqrt (n : ℝ))) := by
  letI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℝ) := by
    simpa [Matrix] using
      (inferInstance : FirstCountableTopology (Fin n → Fin n → ℝ))
  have hselected_tendsto :
      Tendsto algorithm.selectedRadius atTop (𝓝 (Real.sqrt (n : ℝ))) :=
    selectedRadius_tendsto_sqrt_of_sq_gap_bound
      (algorithm := algorithm) htrace_bound hsum
  obtain ⟨Gstar, _, φ, hφmono, hφtendsto⟩ :=
    hcompact.tendsto_subseq (fun k ↦ ⟨k, rfl⟩)
  -- Compactness extracts the convergent matrix subsequence, and the radius limit follows by
  -- composing the already-known convergence with the same strict-mono subsequence.
  have hselected_sub_tendsto :
      Tendsto (algorithm.selectedRadius ∘ φ) atTop (𝓝 (Real.sqrt (n : ℝ))) :=
    hselected_tendsto.comp hφmono.tendsto_atTop
  exact ⟨Gstar, φ, hφmono, hφtendsto, hselected_sub_tendsto⟩

end
