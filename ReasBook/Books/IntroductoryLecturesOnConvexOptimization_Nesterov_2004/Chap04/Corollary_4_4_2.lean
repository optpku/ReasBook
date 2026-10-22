/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped LevelSetNotation Manifold ModifiedGaussNewtonLocalDecreaseNotation Topology
open scoped ModifiedGaussNewtonQuadraticChiNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 L : ℝ} {x0 : E₁}

/- Corollary 4.4.2 lies in the modified Gauss--Newton trajectory / cluster-point domain.

Sampled owner declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate sequence;
* `ModifiedGaussNewtonMethod.meritFunction_succ_le` in `Proposition_4_4_7`, the owner theorem
  keeping the trajectory inside its initial merit sublevel set;
* `ModifiedGaussNewtonMethod.gap_ge_residualSqTail` and
  `ModifiedGaussNewtonMethod.gap_ge_chiWeightedTail` in `Theorem_4_4_1`, the source-facing
  summability owners behind parts `(1)` and `(2)`;
* `cubicRegularization_limitPoints_isConnected` and
  `cubicRegularization_clusterPoint_value_eq_limit` in `Theorem_4_1_2`, the chapter owners for
  connectedness of cluster-point sets and for passing scalar sequence limits to cluster points;
* `modifiedGaussNewtonLocalDecrease` with notation `Δ[problem; φ; r](x)` in `Lemma_4_4_3`, the
  source-facing local-model decrease `Δ_r`.

Best owner abstraction:
* source-facing: the asymptotic consequences for a `ModifiedGaussNewtonMethod`;
* core/canonical: `ModifiedGaussNewtonMethod`, `MapClusterPt`, the initial sublevel set
  `𝓛[f]((f x0))`, and the generic Chapter 4 cluster-point bridge theorems;
* bridge/view: the local-model decrease `Δ[r](x)` and the initial sublevel set
  `𝓛[f]((f x0))`, used internally to pass from trajectory estimates to cluster-point
  consequences.

Primitive data:
* the trajectory `method`;
* the radius parameter `r`.
* for the connected-cluster-set layer, the bounded initial sublevel set `𝓛[f]((f x0))` in a
  proper ambient space;
* for the cluster-point identity layer, continuity of `Δ[r]` at the chosen cluster point.

Internal proof bridges:
* monotonicity of the merit values, confining the trajectory to `𝓛[f]((f x0))`;
* the generic Chapter 4 connected-cluster-set owner
  `cubicRegularization_limitPoints_isConnected`, used after supplying boundedness of `𝓛[f]((f x0))`;
* the scalar cluster-point bridge `cubicRegularization_clusterPoint_value_eq_limit`, used after
  supplying continuity of `Δ[r]` at the cluster point.

Derived API:
* vanishing successive differences;
* vanishing local-model decrease values along the trajectory;
* connectedness of the cluster-point set `X*` under boundedness of `𝓛[f]((f x0))` in a proper
  ambient space;
* the cluster-point identity `Δ_r(x̄) = 0` under continuity of `Δ[problem; φ; r]` at `x̄`.

This file keeps Corollary 4.4.2 source-facing on the intrinsic normed-space layer already used by
`ModifiedGaussNewtonMethod`, while exposing exactly the extra owner-side data needed by the
canonical Chapter 4 cluster-point bridges: boundedness of the initial merit sublevel set in a
proper ambient space for part `(3)`, and continuity of `Δ[r]` at the chosen cluster point for
part `(4)`.
-/

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

namespace ModifiedGaussNewtonMethod

/-- Helper for Corollary 4.4.2: a nonnegative real sequence whose squares converge to `0`
also converges to `0`. -/
private theorem tendsto_zero_of_nonneg_sq_tendsto_zero
    {a : ℕ → ℝ}
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (hsq : Tendsto (fun n ↦ (a n) ^ (2 : ℕ)) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  -- Taking square roots removes the square because the sequence is nonnegative.
  have hsqrt :
      Tendsto (fun n ↦ Real.sqrt ((a n) ^ (2 : ℕ))) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hsq
  convert hsqrt using 1
  ext n
  rw [show (a n) ^ (2 : ℕ) = (a n) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (ha_nonneg n)]

/-- Helper for Corollary 4.4.2: the residual of the accepted whole-space step is exactly the
norm of one iterate difference. -/
private theorem residual_eq_stepDifference_norm
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) :
    r[(method.step k)] (method k) = ‖method k - method (k + 1)‖ := by
  -- Unfold the residual and rewrite the next iterate using the method update rule.
  rw [ModifiedGaussNewtonStep.residualAtUniv_def, method.x_succ k, norm_sub_rev]

-- Proof sketch: apply Theorem 4.4.1 with the canonical lower bound `0 ≤ f x` coming from the
-- sharp merit function, identify `x_{k+1} - x_k` with the residual of the chosen step at `x_k`,
-- and use that summable squared residuals force the residuals themselves to converge to `0`.
/-- Corollary 4.4.2 (1): along a modified Gauss--Newton method, the consecutive differences
`‖x_k - x_{k+1}‖` converge to `0`. -/
theorem stepDifferences_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    Tendsto (fun k ↦ ‖method k - method (k + 1)‖) atTop (𝓝 0) := by
  -- Theorem 4.4.1 makes the residual-square tail summable.
  have hsummable :
      Summable (fun k ↦ (r[(method.step k)] (method k)) ^ (2 : ℕ)) := by
    exact
      (method.gap_ge_residualSqTail
        (fStar := 0)
        (hf_lower := fun z ↦ by
          show 0 ≤ f z
          exact IsMeritFunction.nonneg (φ := φ) (problem z))
        0).1
  have hsq :
      Tendsto
        (fun k ↦ (r[(method.step k)] (method k)) ^ (2 : ℕ))
        atTop
        (𝓝 0) :=
    hsummable.tendsto_atTop_zero
  have hresidual :
      Tendsto (fun k ↦ r[(method.step k)] (method k)) atTop (𝓝 0) :=
    tendsto_zero_of_nonneg_sq_tendsto_zero
      (fun k ↦ by positivity)
      hsq
  -- Route correction: record the residual/step-difference identity as a reusable rewrite.
  simpa [residual_eq_stepDifference_norm] using hresidual

private theorem stepDistances_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    Tendsto (fun k ↦ dist (method (k + 1)) (method k)) atTop (𝓝 0) := by
  simpa [dist_eq_norm, norm_sub_rev] using method.stepDifferences_tendsto_zero

/-- Helper for Corollary 4.4.2: on nonnegative arguments, convergence `χ (tₙ) → 0` forces
`tₙ → 0`. -/
private theorem tendsto_zero_of_nonneg_chi_tendsto_zero
    {t : ℕ → ℝ}
    (ht_nonneg : ∀ n, 0 ≤ t n)
    (hchi : Tendsto (fun n ↦ χ (t n)) atTop (𝓝 0)) :
    Tendsto t atTop (𝓝 0) := by
  -- Eventually `χ (t n)` lies below `1 / 2`, so the affine branch cannot occur.
  have hchi_small : ∀ᶠ n : ℕ in atTop, χ (t n) < 1 / 2 := by
    exact hchi (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have ht_lt_one : ∀ᶠ n : ℕ in atTop, t n < 1 := by
    filter_upwards [hchi_small] with n hn
    by_contra hnot
    have hge : 1 ≤ t n := le_of_not_gt hnot
    have hhalf_le : (1 / 2 : ℝ) ≤ χ (t n) := by
      rw [modifiedGaussNewtonQuadraticChi_of_one_le hge]
      linarith
    linarith
  have hquad_eq :
      (fun n ↦ χ (t n)) =ᶠ[atTop] fun n ↦ (1 / 2 : ℝ) * (t n) ^ (2 : ℕ) := by
    filter_upwards [ht_lt_one] with n hn
    rw [modifiedGaussNewtonQuadraticChi_of_lt_one hn]
  have hquad :
      Tendsto (fun n ↦ (1 / 2 : ℝ) * (t n) ^ (2 : ℕ)) atTop (𝓝 0) :=
    Tendsto.congr' hquad_eq hchi
  -- Multiplying by `2` recovers convergence of the squares.
  have hsq :
      Tendsto (fun n ↦ (t n) ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hscaled :
        Tendsto
          (fun n ↦ (2 : ℝ) * ((1 / 2 : ℝ) * (t n) ^ (2 : ℕ)))
          atTop
          (𝓝 0) := by
      simpa using Filter.Tendsto.const_mul (2 : ℝ) hquad
    simpa [mul_assoc] using hscaled
  exact tendsto_zero_of_nonneg_sq_tendsto_zero ht_nonneg hsq

-- Proof sketch: if `r = 0`, then `Metric.closedBall x 0 = {x}` and the source-facing local model
-- decrease collapses to `Δ_0(x) = 0`. For general `r`, use Theorem 4.4.1 to show that the
-- weighted chi-tail built from `Δ[problem; φ; r](method k)` is summable. Since `χ` is
-- nonnegative and vanishes only at `0`, the summability of this tail forces
-- `Δ_r(method k) → 0`.
/-- Corollary 4.4.2 (2): for every radius `r`, the local model decrease `Δ_r(x_k)` tends to `0`
along the modified Gauss--Newton iterates. -/
theorem localModelDecrease_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (r : NNReal) :
    Tendsto (fun k ↦ Δ[problem; φ; r]((method k))) atTop (𝓝 0) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · -- At radius `0`, every local decrease vanishes identically.
    simpa [localDecrease_zero (problem := problem) (φ := φ)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hvarying :
      Summable
        (fun i ↦
          method.regularization i *
            χ (Δ[problem; φ; r]((method i)) /
              (method.regularization i * (r : ℝ) ^ (2 : ℕ)))) := by
    exact
      (method.gap_ge_chiWeightedTail
        (fStar := 0)
        (hf_lower := fun z ↦ by
          show 0 ≤ f z
          exact IsMeritFunction.nonneg (φ := φ) (problem z))
        0
        r).1
  have hfixed :
      Summable
        (fun i ↦
          (2 * L) *
            χ (Δ[problem; φ; r]((method i)) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ)))) := by
    exact (method.chiWeightedTail_ge_chiWeightedTailAt_two_mul_L 0 r hvarying).1
  have hL_pos : 0 < L := lt_of_lt_of_le method.L0_pos method.L0_le_L
  have h2L_pos : 0 < 2 * L := by positivity
  have hr_ne : (r : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have hr_sq_pos : 0 < (r : ℝ) ^ (2 : ℕ) := by
    have : 0 < (r : ℝ) ^ 2 := sq_pos_of_ne_zero hr_ne
    simpa using this
  let c : ℝ := (2 * L) * (r : ℝ) ^ (2 : ℕ)
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  let t : ℕ → ℝ := fun k ↦ Δ[problem; φ; r]((method k)) / c
  have hweighted :
      Summable (fun k ↦ (2 * L) * χ (t k)) := by
    simpa [t, c] using hfixed
  have hchi_tendsto :
      Tendsto (fun k ↦ χ (t k)) atTop (𝓝 0) := by
    exact
      ((summable_mul_left_iff h2L_pos.ne').1 hweighted).tendsto_atTop_zero
  have ht_nonneg : ∀ k, 0 ≤ t k := by
    intro k
    dsimp [t, c]
    exact div_nonneg
      (modifiedGaussNewton_localDecrease_nonneg problem φ r (method k))
      hc_pos.le
  have ht_tendsto : Tendsto t atTop (𝓝 0) :=
    tendsto_zero_of_nonneg_chi_tendsto_zero ht_nonneg hchi_tendsto
  -- Multiply back by the fixed positive scale to recover `Δ_r(method k)`.
  have hscaled : Tendsto (fun k ↦ c * t k) atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_mul c ht_tendsto
  convert hscaled using 1
  ext k
  dsimp [t, c]
  field_simp [hc_pos.ne']

/-- Helper for Corollary 4.4.2: every cluster point of a sequence that is eventually contained in
a closed set belongs to that set. -/
private theorem clusterPointSet_subset_of_eventually_mem_closed_metric
    {u : ℕ → E₁} {K : Set E₁} (hK_closed : IsClosed K)
    (hmem : ∀ᶠ n : ℕ in atTop, u n ∈ K) :
    {x : E₁ | MapClusterPt x atTop u} ⊆ K := by
  -- Closed eventual tail information propagates to every cluster point.
  intro x hx
  exact hK_closed.mem_of_mapClusterPt hx hmem

/-- Helper for Corollary 4.4.2: if all cluster points of a compact tail lie in an open set, then
the tail is eventually contained in that open set. -/
private theorem eventually_mem_of_clusterPointSet_subset_open_of_eventually_mem_compact_metric
    {u : ℕ → E₁} {K U : Set E₁} (hK : IsCompact K)
    (hmem : ∀ᶠ n : ℕ in atTop, u n ∈ K)
    (hU_open : IsOpen U)
    (hcluster : {x : E₁ | MapClusterPt x atTop u} ⊆ U) :
    ∀ᶠ n : ℕ in atTop, u n ∈ U := by
  by_contra hnot
  -- Otherwise a cluster point would lie in the compact set `K ∩ Uᶜ`.
  have hfreq_notU : ∃ᶠ n : ℕ in atTop, u n ∈ Uᶜ := by
    simpa [Set.mem_compl_iff] using (Filter.not_eventually.mp hnot)
  have hfreq_compact : ∃ᶠ n : ℕ in atTop, u n ∈ K ∩ Uᶜ := by
    simpa [Set.mem_inter_iff] using hmem.and_frequently hfreq_notU
  have hcompact_compl : IsCompact (K ∩ Uᶜ) :=
    hK.inter_right hU_open.isClosed_compl
  rcases hcompact_compl.exists_mapClusterPt_of_frequently hfreq_compact with
    ⟨x, hxKU, hxcluster⟩
  exact hxKU.2 (hcluster hxcluster)

/-- Helper for Corollary 4.4.2: if a tail stays in a disjoint cover by two sets and visits both
sides frequently, then consecutive iterates cross between the two sides infinitely often. -/
private theorem frequently_flips_of_frequently_mem_disjoint_cover_metric
    {u : ℕ → E₁} {s t : Set E₁}
    (hcover : ∀ᶠ n : ℕ in atTop, u n ∈ s ∪ t)
    (hst : Disjoint s t)
    (hs : ∃ᶠ n : ℕ in atTop, u n ∈ s)
    (ht : ∃ᶠ n : ℕ in atTop, u n ∈ t) :
    ∃ᶠ n : ℕ in atTop,
      (u n ∈ s ∧ u (n + 1) ∈ t) ∨ (u n ∈ t ∧ u (n + 1) ∈ s) := by
  classical
  let flip : ℕ → Prop :=
    fun n ↦ (u n ∈ s ∧ u (n + 1) ∈ t) ∨ (u n ∈ t ∧ u (n + 1) ∈ s)
  by_cases hflip : ∃ᶠ n : ℕ in atTop, flip n
  · exact hflip
  · have hno_flip :
        ∀ᶠ n : ℕ in atTop, ¬ flip n :=
      Filter.not_frequently.mp hflip
    -- Once the tail is trapped in one side, frequent visits to the other side are impossible.
    rcases Filter.eventually_atTop.1 (hcover.and hno_flip) with ⟨N, hN⟩
    rcases Filter.frequently_atTop.1 hs N with ⟨n, hnN, hns⟩
    rcases Filter.frequently_atTop.1 ht (max N n) with ⟨m, hmNn, hmt⟩
    have hstay_s : ∀ {k : ℕ}, N ≤ k → u k ∈ s → u (k + 1) ∈ s := by
      intro k hkN hks
      have hk_cover_next : u (k + 1) ∈ s ∪ t :=
        (hN (k + 1) (le_trans hkN (Nat.le_succ k))).1
      have hk_no_flip : ¬ flip k :=
        (hN k hkN).2
      have hk1_not_t : u (k + 1) ∉ t := by
        intro hk1t
        dsimp [flip] at hk_no_flip
        exact hk_no_flip (Or.inl ⟨hks, hk1t⟩)
      rcases hk_cover_next with hk1s | hk1t
      · exact hk1s
      · exact False.elim (hk1_not_t hk1t)
    have htail_s : ∀ d : ℕ, u (n + d) ∈ s := by
      intro d
      induction d with
      | zero =>
          simpa using hns
      | succ d ih =>
          have hkN : N ≤ n + d := le_trans hnN (Nat.le_add_right n d)
          simpa [Nat.add_assoc] using hstay_s hkN ih
    have hnm : n ≤ m := le_trans (le_max_right N n) hmNn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hms : u (n + d) ∈ s := htail_s d
    exact False.elim (hst.le_bot ⟨hms, hmt⟩)

/-- Helper for Corollary 4.4.2: points lying in opposite `δ`-thickenings of well-separated sets
stay at distance larger than `δ`. -/
private theorem lt_dist_of_mem_thickening_of_forall_dist_gt_metric
    {A B : Set E₁} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, 3 * δ < dist a b)
    {x y : E₁}
    (hx : x ∈ Metric.thickening δ A)
    (hy : y ∈ Metric.thickening δ B) :
    δ < dist x y := by
  -- Pull back to witnesses in `A` and `B`, then compare by the triangle inequality.
  rcases (Metric.mem_thickening_iff).1 hx with ⟨a, haA, hxa⟩
  rcases (Metric.mem_thickening_iff).1 hy with ⟨b, hbB, hyb⟩
  have hab_gt : 3 * δ < dist a b := hsep a haA b hbB
  have hab_le : dist a b ≤ dist a x + dist x y + dist y b := by
    calc
      dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
      _ ≤ dist a x + (dist x y + dist y b) := by
        gcongr
        exact dist_triangle _ _ _
      _ = dist a x + dist x y + dist y b := by ring
  have hax_lt : dist a x < δ := by
    simpa [dist_comm] using hxa
  have hyb_lt : dist y b < δ := hyb
  nlinarith

/-- Helper for Corollary 4.4.2: a sequence with compact tail and vanishing successive distances
has connected cluster-point set. -/
private theorem clusterPointSet_isConnected_of_tendsto_dist_zero_on_compact_tail_metric
    {u : ℕ → E₁} {K : Set E₁} (hK : IsCompact K)
    (hmem : ∀ᶠ n : ℕ in atTop, u n ∈ K)
    (hstep :
      Tendsto (fun n : ℕ ↦ dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    IsConnected {x : E₁ | MapClusterPt x atTop u} := by
  let C : Set E₁ := {x : E₁ | MapClusterPt x atTop u}
  have hC_subset : C ⊆ K :=
    clusterPointSet_subset_of_eventually_mem_closed_metric hK.isClosed hmem
  have hC_compact : IsCompact C :=
    hK.of_isClosed_subset isClosed_setOf_clusterPt hC_subset
  have hC_nonempty : C.Nonempty := by
    -- Compactness of the ambient tail produces at least one cluster point.
    rcases hK.exists_mapClusterPt_of_frequently hmem.frequently with ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  refine ⟨hC_nonempty, ?_⟩
  -- Connectedness follows by ruling out persistent jumps between disjoint compact pieces.
  by_contra hC_not_preconnected
  rw [IsPreconnected] at hC_not_preconnected
  push_neg at hC_not_preconnected
  rcases hC_not_preconnected with
    ⟨U, V, hU_open, hV_open, hC_cover, hCU_nonempty, hCV_nonempty, hC_inter_empty⟩
  let A : Set E₁ := C ∩ U
  let B : Set E₁ := C ∩ V
  have hA_nonempty : A.Nonempty := by
    simpa [A] using hCU_nonempty
  have hB_nonempty : B.Nonempty := by
    simpa [B] using hCV_nonempty
  have hA_eq : A = C ∩ Vᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxV
      have hxCUV : x ∈ C ∩ (U ∩ V) := ⟨hx.1, ⟨hx.2, hxV⟩⟩
      have hxEmpty : x ∈ (∅ : Set E₁) := by
        rwa [hC_inter_empty] at hxCUV
      exact hxEmpty.elim
    · intro hx
      refine ⟨hx.1, ?_⟩
      rcases hC_cover hx.1 with hxU | hxV
      · exact hxU
      · exact False.elim (hx.2 hxV)
  have hB_eq : B = C ∩ Uᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxU
      have hxCUV : x ∈ C ∩ (U ∩ V) := ⟨hx.1, ⟨hxU, hx.2⟩⟩
      have hxEmpty : x ∈ (∅ : Set E₁) := by
        rwa [hC_inter_empty] at hxCUV
      exact hxEmpty.elim
    · intro hx
      refine ⟨hx.1, ?_⟩
      rcases hC_cover hx.1 with hxU | hxV
      · exact False.elim (hx.2 hxU)
      · exact hxV
  have hA_compact : IsCompact A := by
    rw [hA_eq]
    exact hC_compact.inter_right hV_open.isClosed_compl
  have hB_compact : IsCompact B := by
    rw [hB_eq]
    exact hC_compact.inter_right hU_open.isClosed_compl
  have hAB_disjoint : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    intro x hxA hxB
    have hxCUV : x ∈ C ∩ (U ∩ V) := ⟨hxA.1, ⟨hxA.2, hxB.2⟩⟩
    have hxEmpty : x ∈ (∅ : Set E₁) := by
      rwa [hC_inter_empty] at hxCUV
    exact hxEmpty.elim
  obtain ⟨r, hr_pos, hsep⟩ :=
    Metric.exists_pos_forall_lt_edist hA_compact hB_compact.isClosed hAB_disjoint
  let δ : ℝ := (r : ℝ) / 3
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hsep_dist : ∀ a ∈ A, ∀ b ∈ B, 3 * δ < dist a b := by
    intro a haA b hbB
    have hr_lt : (r : ℝ) < dist a b := by
      simpa [edist_dist] using hsep a haA b hbB
    dsimp [δ] at *
    nlinarith
  let UA : Set E₁ := Metric.thickening δ A
  let UB : Set E₁ := Metric.thickening δ B
  have hUA_open : IsOpen UA := by
    simpa [UA] using (Metric.isOpen_thickening : IsOpen (Metric.thickening δ A))
  have hUB_open : IsOpen UB := by
    simpa [UB] using (Metric.isOpen_thickening : IsOpen (Metric.thickening δ B))
  have hA_subset_UA : A ⊆ UA := by
    simpa [UA] using Metric.self_subset_thickening hδ_pos A
  have hB_subset_UB : B ⊆ UB := by
    simpa [UB] using Metric.self_subset_thickening hδ_pos B
  have hUAUB_disjoint : Disjoint UA UB := by
    refine Set.disjoint_left.2 ?_
    intro x hxUA hxUB
    have hlt : δ < dist x x := by
      exact
        lt_dist_of_mem_thickening_of_forall_dist_gt_metric
          hδ_pos
          hsep_dist
          hxUA
          hxUB
    have : δ < 0 := by
      simpa using hlt
    exact not_lt_of_ge hδ_pos.le this
  have hC_subset_union : C ⊆ UA ∪ UB := by
    intro x hxC
    rcases hC_cover hxC with hxU | hxV
    · exact Or.inl (hA_subset_UA ⟨hxC, hxU⟩)
    · exact Or.inr (hB_subset_UB ⟨hxC, hxV⟩)
  have htail_union : ∀ᶠ n : ℕ in atTop, u n ∈ UA ∪ UB :=
    eventually_mem_of_clusterPointSet_subset_open_of_eventually_mem_compact_metric
      hK
      hmem
      (hUA_open.union hUB_open)
      hC_subset_union
  obtain ⟨a, haA⟩ := hA_nonempty
  obtain ⟨b, hbB⟩ := hB_nonempty
  have hfreq_UA : ∃ᶠ n : ℕ in atTop, u n ∈ UA := by
    -- A cluster point in `A` forces infinitely many visits to every neighborhood of `A`.
    have ha_nhds : UA ∈ 𝓝 a :=
      hUA_open.mem_nhds (hA_subset_UA haA)
    exact (show MapClusterPt a atTop u from haA.1).frequently ha_nhds
  have hfreq_UB : ∃ᶠ n : ℕ in atTop, u n ∈ UB := by
    -- The same holds for a cluster point in `B`.
    have hb_nhds : UB ∈ 𝓝 b :=
      hUB_open.mem_nhds (hB_subset_UB hbB)
    exact (show MapClusterPt b atTop u from hbB.1).frequently hb_nhds
  have hflip :
      ∃ᶠ n : ℕ in atTop,
        (u n ∈ UA ∧ u (n + 1) ∈ UB) ∨ (u n ∈ UB ∧ u (n + 1) ∈ UA) :=
    frequently_flips_of_frequently_mem_disjoint_cover_metric
      htail_union
      hUAUB_disjoint
      hfreq_UA
      hfreq_UB
  have hstep_small : ∀ᶠ n : ℕ in atTop, dist (u (n + 1)) (u n) < δ :=
    hstep (Iio_mem_nhds hδ_pos)
  have hstep_large :
      ∃ᶠ n : ℕ in atTop, δ < dist (u (n + 1)) (u n) := by
    -- Crossing between the two thickenings forces a uniform positive jump.
    refine hflip.mono ?_
    intro n hn
    rcases hn with hAB | hBA
    · simpa [dist_comm] using
        (lt_dist_of_mem_thickening_of_forall_dist_gt_metric
          hδ_pos
          hsep_dist
          hAB.1
          hAB.2)
    · exact
        lt_dist_of_mem_thickening_of_forall_dist_gt_metric
          hδ_pos
          hsep_dist
          hBA.2
          hBA.1
  have hstep_not_large : ∀ᶠ n : ℕ in atTop, ¬ δ < dist (u (n + 1)) (u n) := by
    filter_upwards [hstep_small] with n hsmall
    exact not_lt_of_ge hsmall.le
  exact (Filter.not_frequently.mpr hstep_not_large) hstep_large

-- Proof sketch: use Proposition 4.4.7 to keep the entire trajectory inside the initial sublevel
-- set `𝓛0`, upgrade boundedness of `𝓛0` to compactness of `closure 𝓛0` in the proper ambient
-- space, and then apply the local compact-tail no-oscillation lemma proved above.
/-- Corollary 4.4.2 (3): the set `X*` of limit points of the modified Gauss--Newton trajectory is
connected provided the initial merit sublevel set `𝓛[f]((f x₀))` is bounded in the proper
ambient space. -/
theorem limitPoints_isConnected
    [ProperSpace E₁]
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (hbounded : Bornology.IsBounded 𝓛0) :
    IsConnected {xBar : E₁ | MapClusterPt xBar atTop method} := by
  let K : Set E₁ := closure 𝓛0
  have hcompact : IsCompact K := by
    simpa [K] using hbounded.isCompact_closure
  have hmem_level : ∀ k : ℕ, method k ∈ 𝓛0 := by
    intro k
    rw [mem_levelSet_iff]
    calc
      f (method k) ≤ f (method 0) := method.meritFunction_antitone (Nat.zero_le k)
      _ = f x0 := by rw [method.x_zero]
  have htail : ∀ᶠ k : ℕ in atTop, method k ∈ K := by
    exact Filter.Eventually.of_forall fun k ↦ subset_closure (hmem_level k)
  -- The metric compact-tail bridge now gives connectedness of the cluster-point set.
  simpa [K] using
    clusterPointSet_isConnected_of_tendsto_dist_zero_on_compact_tail_metric
      hcompact
      htail
      method.stepDistances_tendsto_zero

-- Proof sketch: extract a subsequence converging to the cluster point, compose part `(2)` with
-- that subsequence to get scalar convergence to `0`, compose continuity of `Δ_r` with the same
-- subsequence to get convergence to `Δ_r(x̄)`, and conclude by uniqueness of limits.
/-- Corollary 4.4.2 (4): every cluster point `x̄ ∈ X*` of the modified Gauss--Newton trajectory
satisfies `Δ_r(x̄) = 0` for each radius `r`, provided `Δ[problem; φ; r]` is continuous at `x̄`. -/
theorem clusterPoint_localModelDecrease_eq_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (r : NNReal)
    {xBar : E₁} (hxBar : MapClusterPt xBar atTop method)
    (hΔ_cont : ContinuousAt (fun x ↦ Δ[problem; φ; r](x)) xBar) :
    Δ[problem; φ; r](xBar) = 0 := by
  rcases hxBar.exists_seq_tendsto with ⟨ψ, hsubseq, hψ_tendsto⟩
  have hΔ_limit :
      Tendsto (fun k ↦ Δ[problem; φ; r]((method k))) atTop (𝓝 0) :=
    method.localModelDecrease_tendsto_zero r
  have hΔ_subseq :
      Tendsto (fun n ↦ Δ[problem; φ; r]((method (ψ n)))) atTop (𝓝 0) := by
    simpa [Function.comp] using hΔ_limit.comp hψ_tendsto
  have hΔ_point :
      Tendsto (fun n ↦ Δ[problem; φ; r]((method (ψ n))))
        atTop
        (𝓝 (Δ[problem; φ; r](xBar))) :=
    hΔ_cont.tendsto.comp hsubseq
  exact tendsto_nhds_unique hΔ_point hΔ_subseq

end ModifiedGaussNewtonMethod

end
