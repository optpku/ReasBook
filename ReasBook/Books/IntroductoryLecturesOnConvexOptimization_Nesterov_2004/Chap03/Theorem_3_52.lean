/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_52
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_53

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

attribute [local instance] Classical.decPred

section Euclidean

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {Q : Set E} {xStar : E} {g : E → E} {querySeq : ℕ → E} {Ell : ℕ → Set E}
variable {D : ℝ} {k : ℕ}

local notation "X" => feasibleSubsequence Q querySeq
local notation "m" => Nat.count (fun j ↦ querySeq j ∈ Q) k
local notation "S" => localizationSets Q X (g ∘ X)

/-
Primary domain: localization-radius bounds along the canonical feasible subsequence of a
cutting-plane query history.

Sampled owner-style declarations in the same domain:
- `Nat.count`, `feasibleSubsequence`, and `feasibleSubsequence_count_eq_self_of_feasible` from
  `Definition_3_53`, the chapter owners for the selected feasible index `i(k)` and the
  corresponding selected sequence;
- `localizationSets` and `localizationSets_zero` from `Definition_3_52`, the source-facing
  recursive localization family `S_j`;
- `localizationSets_succ_eq_localizationSet` from `Definition_3_52`, the canonical bridge from the
  recursive family to the earlier closed-form stage owner;
- `localization_radius` and
  `localization_radius_le_outer_radius_mul_volume_ratio_rpow` from `Theorem_3_2_9`, the owner
  localization radius `v_j^*` and its stagewise volume bound.

Best owner abstraction:
- source-facing: the selected feasible counter `Nat.count (fun j ↦ querySeq j ∈ Q) k`, the
  selected feasible sequence `feasibleSubsequence Q querySeq`, and the recursive localization sets
  `localizationSets`;
- core/canonical: `localization_radius` together with
  `localization_radius_le_outer_radius_mul_volume_ratio_rpow`;
- bridge/view: comparison of the selected recursive localization stage with an external ambient
  set sequence `Ell`.

Primitive data:
- the feasible set `Q`;
- the raw query history `querySeq`;
- the localization-measure owner map `g`;
- the ambient comparison sequence `Ell`.

Derived API:
- the selected feasible index `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- the selected feasible sequence `feasibleSubsequence Q querySeq`;
- the selected localization stage
  `localizationSets Q (feasibleSubsequence Q querySeq) (g ∘ feasibleSubsequence Q querySeq)`;
- the corresponding owner radius
  `localization_radius xStar g (feasibleSubsequence Q querySeq)`;
- the selected-stage radius bound and the positivity consequence of strict volume drop.

Accordingly this file stays at the bridge/view layer, but it now grows directly from the chapter
owners `Nat.count`, `feasibleSubsequence`, `localizationSets`, and `localization_radius` instead
of a parallel local API on arbitrary `S`, `vStar`, and `i`.
-/

/-- Helper for Theorem 3.52: a positive selected-feasible count guarantees that the first selected
query is genuinely feasible, rather than the fallback value of `Nat.nth`. -/
lemma selected_zero_mem_of_positive_count
    (hik : 0 < m) :
    X 0 ∈ Q := by
  -- A positive count forces `Nat.nth` at index `0` to hit an actual feasible query.
  have hmem :
      querySeq (Nat.nth (fun j ↦ querySeq j ∈ Q) 0) ∈ Q := by
    simpa using
      (Nat.nth_mem 0 fun hf ↦ hik.trans_le (Nat.count_le_card hf k))
  simpa [X, feasibleSubsequence] using hmem

/-- Helper for Theorem 3.52: every positive selected stage is still contained in the initial set
`Q`, because `localizationSets` is defined by intersecting with `Q` at every step. -/
lemma selected_stage_subset_domain
    (j : ℕ) :
    S (j + 1) ⊆ Q := by
  -- Rewrite the recursive stage into the closed-form localization-set owner and project to `Q`.
  rw [localizationSets_succ_eq_localizationSet]
  intro x hx
  exact hx.1

/-- Helper for Theorem 3.52: the first selected point lies in the outer ball, so its pointwise
localization measure is bounded by the same radius `D`. -/
lemma selected_zero_measure_le_outer_radius
    (hxStar : xStar ∈ Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hX0 : X 0 ∈ Q) :
    subgradientLocalizationMeasure g xStar (X 0) ≤ D := by
  -- The outer-ball hypothesis gives the geometric distance bound for the first selected point.
  have hD_nonneg : 0 ≤ D := by
    have hxBall : xStar ∈ Metric.closedBall xStar D := hQ_subset hxStar
    simpa [Metric.mem_closedBall] using hxBall
  have hdist : ‖X 0 - xStar‖ ≤ D := by
    simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm] using hQ_subset hX0
  by_cases hzero : g (X 0) = 0
  · -- If the chosen cut vector vanishes, the localization measure is `0`.
    simpa [subgradientLocalizationMeasure, hzero] using hD_nonneg
  · -- Otherwise Cauchy-Schwarz turns the normalized inner product into a distance bound.
    simp [subgradientLocalizationMeasure, hzero]
    have hinner_le :
        inner ℝ (g (X 0)) (X 0 - xStar) ≤ ‖g (X 0)‖ * ‖X 0 - xStar‖ := by
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    have hnorm_pos : 0 < ‖g (X 0)‖ := norm_pos_iff.mpr hzero
    have hratio_le :
        inner ℝ (g (X 0)) (X 0 - xStar) / ‖g (X 0)‖ ≤ ‖X 0 - xStar‖ := by
      exact (div_le_iff₀ hnorm_pos).2 <| by simpa [mul_comm] using hinner_le
    exact hratio_le.trans hdist

/-- Helper for Theorem 3.52: every selected localization radius is bounded by the outer radius
`D`, because the first selected feasible point already has pointwise localization measure at most
`D`. -/
lemma selected_radius_le_outer_radius
    (hxStar : xStar ∈ Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hX0 : X 0 ∈ Q)
    (j : ℕ) :
    (localization_radius xStar g X j : ℝ) ≤ D := by
  -- The prefix minimum defining `localization_radius` is at most its first sampled measure.
  have hmeasure0 : subgradientLocalizationMeasure g xStar (X 0) ≤ D :=
    selected_zero_measure_le_outer_radius hxStar hQ_subset hX0
  exact (localization_radius_le_measure (xStar := xStar) (g := g) (xSeq := X) (k := j) 0).trans
    hmeasure0

/-- Helper for Theorem 3.52: any closed ball whose radius is below the selected localization radius
is contained in the corresponding selected localization stage. -/
lemma closedBall_inter_subset_selected_stage
    {j : ℕ} {r : NNReal}
    (hr : (r : ℝ) ≤ localization_radius xStar g X j) :
    Metric.closedBall xStar r ∩ Q ⊆ S (j + 1) := by
  -- Route correction: instead of using the imported placeholder theorem for this inclusion,
  -- prove it directly from the closed-form description of `localizationSet`.
  rw [localizationSets_succ_eq_localizationSet]
  intro x hx
  rw [mem_localizationSet_iff]
  constructor
  · exact hx.2
  · intro i
    have hri :
        (r : ℝ) ≤ subgradientLocalizationMeasure g xStar (X i) :=
      hr.trans (localization_radius_le_measure (xStar := xStar) (g := g) (xSeq := X) (k := j) i)
    have hx_norm : ‖x - xStar‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm] using hx.1
    by_cases hzero : g (X i) = 0
    · -- A zero cut vector makes the half-space inequality trivial.
      simp [hzero]
    · -- Otherwise compare the support inequality with the Cauchy-Schwarz bound on the ball.
      have hnorm_pos : 0 < ‖g (X i)‖ := norm_pos_iff.mpr hzero
      have hsource :
          (r : ℝ) * ‖g (X i)‖ ≤ inner ℝ (g (X i)) (X i - xStar) := by
        simp [subgradientLocalizationMeasure, hzero] at hri
        exact (le_div_iff₀ hnorm_pos).mp hri
      have hball_inner :
          inner ℝ (g (X i)) (x - xStar) ≤ ‖g (X i)‖ * (r : ℝ) := by
        have hinner_le :
            inner ℝ (g (X i)) (x - xStar) ≤ ‖g (X i)‖ * ‖x - xStar‖ := by
          exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
        exact hinner_le.trans (mul_le_mul_of_nonneg_left hx_norm (norm_nonneg _))
      have hcompare :
          inner ℝ (g (X i)) (x - xStar) ≤ inner ℝ (g (X i)) (X i - xStar) := by
        linarith
      have hsub : X i - x = (X i - xStar) - (x - xStar) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hdecomp :
          inner ℝ (g (X i)) (X i - x) =
            inner ℝ (g (X i)) (X i - xStar) - inner ℝ (g (X i)) (x - xStar) := by
        rw [hsub, inner_sub_right]
      rw [Function.comp_apply, hdecomp]
      linarith

/-- Helper for Theorem 3.52: the positive selected stage satisfies the intrinsic volume-ratio
bound, proved locally so that the proof only uses the explicit homothety branch. -/
lemma selected_stage_radius_bound_succ
    (hn : 0 < n)
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < volume.real Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hX0 : X 0 ∈ Q)
    (j : ℕ) :
    (localization_radius xStar g X j : ℝ) ≤
      D * Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) := by
  -- The outer radius is strictly positive because `Q` has positive volume and contains `xStar`.
  have hdim : 0 < Module.finrank ℝ E := by
    change 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
    simpa using hn
  have hD_pos : 0 < D := by
    exact outer_radius_pos_of_positive_measure (μ := volume) hdim hxStar hQ_pos hQ_subset
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  have hstage_finite : volume (S (j + 1)) ≠ ⊤ := by
    -- The selected stage stays inside `Q`, hence inside the finite-volume outer ball.
    have hsubset_ball : S (j + 1) ⊆ Metric.closedBall xStar D := by
      intro x hx
      exact hQ_subset (selected_stage_subset_domain (Q := Q) (g := g) (querySeq := querySeq) j hx)
    exact measure_ne_top_of_subset hsubset_ball measure_closedBall_lt_top.ne
  by_cases hloc_nonneg : 0 ≤ (localization_radius xStar g X j : ℝ)
  · -- In the nonnegative branch, normalize the radius by `D` and run the homothety argument.
    have hloc_le_D :
        (localization_radius xStar g X j : ℝ) ≤ D :=
      selected_radius_le_outer_radius hxStar hQ_subset hX0 j
    let α : ℝ := localization_radius xStar g X j / D
    have hα0 : 0 ≤ α := by
      exact div_nonneg hloc_nonneg hD_nonneg
    have hα1 : α ≤ 1 := by
      exact (div_le_iff₀ hD_pos).2 (by simpa [α] using hloc_le_D)
    have hα_mul : α * D = localization_radius xStar g X j := by
      dsimp [α]
      field_simp [hD_pos.ne']
    let r : NNReal := ⟨localization_radius xStar g X j, hloc_nonneg⟩
    have hball :
        Metric.closedBall xStar (localization_radius xStar g X j) ∩ Q ⊆ S (j + 1) := by
      simpa [r] using
        (closedBall_inter_subset_selected_stage
          (Q := Q) (xStar := xStar) (g := g) (querySeq := querySeq)
          (j := j) (r := r) le_rfl)
    have himage_subset :
        AffineMap.homothety xStar α '' Q ⊆
          Metric.closedBall xStar (localization_radius xStar g X j) ∩ Q := by
      -- The source proof uses the normalized homothety image as the canonical comparison set.
      have hsubset :=
        homothety_image_subset_closedBall_inter_of_convex
          hα0 hα1 hQ_convex hxStar hQ_subset
      simpa [hα_mul] using hsubset
    have hmeasure_mono :
        volume.real (AffineMap.homothety xStar α '' Q) ≤ volume.real (S (j + 1)) := by
      exact measureReal_mono (fun z hz ↦ hball (himage_subset hz)) hstage_finite
    have hmeasure_scaled :
        α ^ n * volume.real Q ≤ volume.real (S (j + 1)) := by
      simpa [measureReal_homothety_image (μ := volume) (Q := Q) (xStar := xStar) hα0]
        using hmeasure_mono
    have hα_le :
        α ≤ Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) := by
      simpa using
        (alpha_le_volume_ratio_rpow_of_measure_bound
          (μ := volume) hdim hQ_pos hα0 hmeasure_scaled)
    calc
      (localization_radius xStar g X j : ℝ) = α * D := by
        rw [hα_mul]
      _ ≤ Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) * D := by
        exact mul_le_mul_of_nonneg_right hα_le hD_nonneg
      _ = D * Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) := by
        ring
  · -- If the selected radius is nonpositive, the target bound is immediate from nonnegativity.
    have hratio_nonneg : 0 ≤ volume.real (S (j + 1)) / volume.real Q := by
      positivity
    have hbound_nonneg :
        0 ≤ D * Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) := by
      exact mul_nonneg hD_nonneg (Real.rpow_nonneg hratio_nonneg _)
    exact (le_of_not_ge hloc_nonneg).trans hbound_nonneg

/-- Helper for Theorem 3.52: volume monotonicity turns the selected-stage ratio bound into the
ambient comparison ratio bound. -/
lemma selected_stage_real_ratio_mono
    (j : ℕ)
    (hQ_pos : 0 < volume.real Q)
    (hEll_finite : volume (Ell k) ≠ ⊤)
    (hD_nonneg : 0 ≤ D)
    (hvol : volume (S (j + 1)) ≤ volume (Ell k)) :
    D * Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) ≤
      D * Real.rpow (volume.real (Ell k) / volume.real Q) ((1 : ℝ) / n) := by
  -- Convert the ENNReal measure comparison to real ratios and apply monotonicity of `rpow`.
  have hvol_real : volume.real (S (j + 1)) ≤ volume.real (Ell k) := by
    simpa using ENNReal.toReal_mono hEll_finite hvol
  have hratio :
      volume.real (S (j + 1)) / volume.real Q ≤ volume.real (Ell k) / volume.real Q :=
    div_le_div_of_nonneg_right hvol_real hQ_pos.le
  have hratio_nonneg : 0 ≤ volume.real (S (j + 1)) / volume.real Q := by
    positivity
  have hexp_nonneg : 0 ≤ (1 : ℝ) / n := by
    positivity
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hratio_nonneg hratio hexp_nonneg)
    hD_nonneg

/-- Theorem 3.52 (1): let `i(k) = Nat.count (fun j ↦ querySeq j ∈ Q) k` be the canonical selected
feasible index and let `X = feasibleSubsequence Q querySeq` be the corresponding selected
sequence. If `i(k)` is positive, if the stage-`i(k)` recursive localization set of `X` has volume
at most the ambient comparison volume `vol_n Ell_k`, and if the chapter owner bound for the
localization radius is available, then the selected localization radius is bounded first by the
selected localization-stage volume ratio and then by the ambient comparison volume ratio. -/
theorem selected_radius_bound_of_positive_index
    (hn : 0 < n)
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < volume.real Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hEll_finite : volume (Ell k) ≠ ⊤)
    (hvol : volume (S m) ≤ volume (Ell k))
    (hik : 0 < m) :
    (localization_radius xStar g X (m - 1) : ℝ) ≤
        D * Real.rpow (volume.real (S m) / volume.real Q) ((1 : ℝ) / n) ∧
      D *
          Real.rpow (volume.real (S m) / volume.real Q) ((1 : ℝ) / n) ≤
        D * Real.rpow (volume.real (Ell k) / volume.real Q) ((1 : ℝ) / n) := by
  -- Rewrite the positive selected index as a successor, matching the recursive stage owner.
  have hX0 : X 0 ∈ Q :=
    selected_zero_mem_of_positive_count hik
  have hD_nonneg : 0 ≤ D := by
    have hxBall : xStar ∈ Metric.closedBall xStar D := hQ_subset hxStar
    simpa [Metric.mem_closedBall] using hxBall
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hik) with ⟨j, hm⟩
  rw [hm] at hvol ⊢
  have hstage :
      (localization_radius xStar g X j : ℝ) ≤
        D * Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) :=
    selected_stage_radius_bound_succ
      hn hQ_convex hxStar hQ_pos hQ_subset hX0 j
  have hcompare :
      D * Real.rpow (volume.real (S (j + 1)) / volume.real Q) ((1 : ℝ) / n) ≤
        D * Real.rpow (volume.real (Ell k) / volume.real Q) ((1 : ℝ) / n) :=
    selected_stage_real_ratio_mono
      j hQ_pos hEll_finite hD_nonneg hvol
  simpa using And.intro hstage hcompare

end Euclidean

section Ambient

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
variable {μ : Measure E}
variable {Q : Set E} {g : E → E} {querySeq : ℕ → E} {Ell : ℕ → Set E}
variable {k : ℕ}

local notation "X" => feasibleSubsequence Q querySeq
local notation "m" => Nat.count (fun j ↦ querySeq j ∈ Q) k
local notation "S" => localizationSets Q X (g ∘ X)

/-- Theorem 3.52 (2): with the same canonical selected feasible index
`i(k) = Nat.count (fun j ↦ querySeq j ∈ Q) k` and selected sequence
`X = feasibleSubsequence Q querySeq`, if the selected recursive localization stage has volume at
most `vol_n Ell_k` and the ambient comparison volume is strictly smaller than `vol_n Q`, then the
selected feasible index is positive. -/
theorem selected_index_pos_of_volume_drop
    (hvol : μ (S m) ≤ μ (Ell k))
    (hEll_lt : μ (Ell k) < μ Q) :
    0 < m := by
  by_contra hm
  have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm
  have hQ_le : μ Q ≤ μ (Ell k) := by
    simpa [hm_zero, localizationSets_zero] using hvol
  exact not_lt_of_ge hQ_le hEll_lt

end Ambient

end
