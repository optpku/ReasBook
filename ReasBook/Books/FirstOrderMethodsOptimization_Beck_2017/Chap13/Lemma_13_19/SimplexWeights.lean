/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_16

-- Theorem-local helpers for Lemma 13.19.

noncomputable section

open Filter
open scoped BigOperators Topology

section

variable {l : ℕ}
variable {lam : ℕ → ℝ} {i : ℕ → Fin l} {v0 : stdSimplex ℝ (Fin l)}

/-- Helper for Lemma 13.19: the generic barycentric recursion
`v^{k+1} = (1 - λ_k) v^k + λ_k e_{i_k}` on the standard simplex. -/
def simplex_vertex_weight_recursion
    (lam : ℕ → ℝ) (i : ℕ → Fin l) (w0 : Fin l → ℝ) : ℕ → Fin l → ℝ :=
  Nat.rec w0 fun k wk j ↦
    (1 - lam k) * wk j + lam k * if j = i k then 1 else 0

local notation "w[" k "]" =>
  simplex_vertex_weight_recursion lam i (v0 : Fin l → ℝ) k

/-- Helper for Lemma 13.19: the generic simplex-weight recursion preserves membership in the
standard simplex under `0 ≤ λ_k ≤ 1`. -/
lemma simplex_vertex_weight_recursion_mem_stdSimplex
    (h_nonneg : ∀ k, 0 ≤ lam k)
    (h_le_one : ∀ k, lam k ≤ 1) :
    ∀ k, w[k] ∈ stdSimplex ℝ (Fin l)
  | 0 => by
      -- The recursion starts from the initial simplex point.
      change (v0 : Fin l → ℝ) ∈ stdSimplex ℝ (Fin l)
      exact v0.property
  | k + 1 => by
      have hk := simplex_vertex_weight_recursion_mem_stdSimplex h_nonneg h_le_one k
      refine ⟨?_, ?_⟩
      · -- Each coordinate stays nonnegative because the update is a convex combination of
        -- nonnegative coordinates and the chosen simplex vertex.
        intro j
        have hindicator_nonneg : 0 ≤ if j = i k then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        have hw_nonneg : 0 ≤ w[k] j := hk.1 j
        simpa [simplex_vertex_weight_recursion] using
          add_nonneg
            (mul_nonneg (sub_nonneg.mpr (h_le_one k)) hw_nonneg)
            (mul_nonneg (h_nonneg k) hindicator_nonneg)
      · -- The updated coordinates still sum to one because the coefficients form a convex
        -- combination of the previous simplex point and the selected simplex vertex.
        have hindicator_sum :
            (∑ j : Fin l, (if j = i k then (1 : ℝ) else 0)) = 1 := by
          simp
        calc
          ∑ j : Fin l, w[k + 1] j
              = ∑ j : Fin l, ((1 - lam k) * w[k] j + lam k * if j = i k then 1 else 0) := by
                  simp [simplex_vertex_weight_recursion]
          _ = ∑ j : Fin l, ((1 - lam k) * w[k] j) +
                ∑ j : Fin l, (lam k * if j = i k then 1 else 0) := by
                rw [Finset.sum_add_distrib]
          _ = (1 - lam k) * ∑ j : Fin l, w[k] j +
                lam k * ∑ j : Fin l, (if j = i k then 1 else 0) := by
                rw [Finset.mul_sum, Finset.mul_sum]
          _ = (1 - lam k) * 1 + lam k * 1 := by
                rw [hk.2, hindicator_sum]
          _ = 1 := by
                ring

/-- Helper for Lemma 13.19: every generic barycentric coordinate stays above the initial
coordinate times the complementary product `∏_{n<k} (1 - λ_n)`. -/
lemma simplex_vertex_weight_recursion_prod_lower_bound
    (h_nonneg : ∀ k, 0 ≤ lam k)
    (h_le_one : ∀ k, lam k ≤ 1) :
    ∀ k j, (∏ n ∈ Finset.range k, (1 - lam n)) * v0 j ≤ w[k] j
  | 0, j => by
      -- The empty product is `1`, so the recursion starts at equality.
      simp [simplex_vertex_weight_recursion]
  | k + 1, j => by
      have hk := simplex_vertex_weight_recursion_prod_lower_bound h_nonneg h_le_one k j
      have hindicator_nonneg :
          0 ≤ lam k * if j = i k then (1 : ℝ) else 0 := by
        have : 0 ≤ if j = i k then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        exact mul_nonneg (h_nonneg k) this
      calc
        (∏ n ∈ Finset.range (k + 1), (1 - lam n)) * v0 j
            = ((∏ n ∈ Finset.range k, (1 - lam n)) * (1 - lam k)) * v0 j := by
                simp [Finset.prod_range_succ]
        _ = (1 - lam k) * ((∏ n ∈ Finset.range k, (1 - lam n)) * v0 j) := by
              ring
        _ ≤ (1 - lam k) * w[k] j := by
              exact mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr (h_le_one k))
        _ ≤ (1 - lam k) * w[k] j + lam k * if j = i k then 1 else 0 := by
              exact le_add_of_nonneg_right hindicator_nonneg
        _ = w[k + 1] j := by
              simp [simplex_vertex_weight_recursion]

/-- Helper for Lemma 13.19: if the generic stepsizes are summable and satisfy `0 ≤ λ_k < 1`,
then every barycentric coordinate stays uniformly above a positive multiple of its initial value. -/
lemma simplex_vertex_weight_recursion_lower_bound_of_summable
    (h_nonneg : ∀ k, 0 ≤ lam k)
    (h_lt_one : ∀ k, lam k < 1)
    (hs : Summable lam) :
    ∃ δ > 0, ∀ k j, δ * v0 j ≤ w[k] j := by
  let p : ℕ → ℝ := fun k ↦ ∏ n ∈ Finset.range k, (1 - lam n)
  have hp_pos : ∀ k, 0 < p k := by
    -- Every complementary product is positive because each factor lies in `(0, 1]`.
    intro k
    dsimp [p]
    refine Finset.prod_pos ?_
    intro n hn
    exact sub_pos.mpr (h_lt_one n)
  have hp_tendsto :
      Filter.Tendsto p Filter.atTop (nhds (∏' n, (1 - lam n))) := by
    have hmul : Multipliable (fun n : ℕ ↦ 1 - lam n) := by
      simpa [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs.neg
    -- The canonical partial products converge to the infinite product.
    simpa [p] using hmul.tendsto_prod_tprod_nat
  have htprod_nonneg : 0 ≤ ∏' n, (1 - lam n) := by
    -- Nonnegativity of the finite complementary products passes to the infinite-product limit.
    refine isClosed_Ici.mem_of_tendsto hp_tendsto ?_
    exact Filter.Eventually.of_forall fun k ↦ by
      dsimp [p]
      exact Finset.prod_nonneg fun n hn ↦ sub_nonneg.mpr (h_lt_one n).le
  have htprod_ne_zero :
      ∏' n, (1 - lam n) ≠ 0 :=
    tprod_one_sub_ne_zero_of_summable h_nonneg h_lt_one hs
  have htprod_pos : 0 < ∏' n, (1 - lam n) := by
    exact lt_of_le_of_ne htprod_nonneg htprod_ne_zero.symm
  have hp_eventually :
      ∀ᶠ k : ℕ in Filter.atTop, (∏' n, (1 - lam n)) / 2 < p k := by
    -- A positive infinite-product limit forces the tail complementary products to stay
    -- uniformly positive.
    have hhalf_lt : (∏' n, (1 - lam n)) / 2 < ∏' n, (1 - lam n) := by
      nlinarith
    exact hp_tendsto.eventually (Ioi_mem_nhds hhalf_lt)
  rcases Filter.eventually_atTop.mp hp_eventually with ⟨N, hN⟩
  let δ : ℝ :=
    min ((∏' n, (1 - lam n)) / 2)
      (Finset.inf' (Finset.range (N + 1)) (by simp) p)
  have hδ_pos : 0 < δ := by
    -- The minimum of the positive tail bound and the finitely many initial products is positive.
    refine lt_min ?_ ?_
    · nlinarith
    · exact (Finset.lt_inf'_iff (by simp)).2 fun k hk ↦ hp_pos k
  refine ⟨δ, hδ_pos, ?_⟩
  intro k j
  have hδ_le_p : δ ≤ p k := by
    by_cases hk : k ≤ N
    · exact le_trans (min_le_right _ _) (Finset.inf'_le _ (by simpa using hk))
    · have hNk : N ≤ k := Nat.le_of_not_ge hk
      exact le_trans (min_le_left _ _) (le_of_lt (hN k hNk))
  have hv0_nonneg : 0 ≤ v0 j := stdSimplex.zero_le v0 j
  exact le_trans
    (mul_le_mul_of_nonneg_right hδ_le_p hv0_nonneg)
    (simplex_vertex_weight_recursion_prod_lower_bound h_nonneg (fun k ↦ (h_lt_one k).le) k j)

end
