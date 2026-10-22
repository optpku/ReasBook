/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private lemma bounded_range_of_tendsto_toWeakSpace {x : ℕ → H} {y : H}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H y))) :
    Bornology.IsBounded (Set.range x) := by
  let T : ℕ → H →L[ℝ] ℝ := fun n ↦ InnerProductSpace.toDual ℝ H (x n)
  have hB_inj : Function.Injective ((topDualPairing ℝ H).flip) := by
    intro z w hzw
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hne
    exact hf (DFunLike.congr_fun hzw f)
  have hpointwise : ∀ u : H, ∃ C : ℝ, ∀ n : ℕ, ‖T n u‖ ≤ C := by
    intro u
    have hu_tendsto : Tendsto (fun n ↦ inner ℝ u (x n)) atTop (𝓝 (inner ℝ u y)) := by
      have hEval :=
        (WeakBilin.tendsto_iff_forall_eval_tendsto ((topDualPairing ℝ H).flip) hB_inj).1 hy
          (InnerProductSpace.toDual ℝ H u)
      simpa [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace] using hEval
    have hu_bounded : Bornology.IsBounded (Set.range fun n ↦ inner ℝ u (x n)) :=
      Metric.isBounded_range_of_tendsto _ hu_tendsto
    rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    have hCn : ‖inner ℝ u (x n)‖ ≤ C := hC _ (Set.mem_range_self n)
    simpa [T, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hCn
  obtain ⟨C, hC⟩ := banach_steinhaus hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro z ⟨n, rfl⟩
  have hTn : ‖T n‖ ≤ C := hC n
  change ‖InnerProductSpace.toDual ℝ H (x n)‖ ≤ C at hTn
  rw [(InnerProductSpace.toDual ℝ H).norm_map] at hTn
  exact hTn

private lemma tendsto_inner_sub_right_zero {x : ℕ → H} {y v : H}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto (fun n ↦ ⟪x n - y, v⟫_ℝ) atTop (𝓝 0) := by
  have hEval :=
    ((WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
      (InnerProductSpace.toDual ℝ H v)).tendsto (toWeakSpace ℝ H y)).comp hy
  have hEval' : Tendsto (fun n ↦ ⟪v, x n⟫_ℝ) atTop (𝓝 (⟪v, y⟫_ℝ)) := by
    simpa only [toWeakSpace, LinearEquiv.refl_apply, LinearMap.flip_apply,
      topDualPairing_apply, InnerProductSpace.toDual_apply_apply] using hEval
  have hsub :
      Tendsto (fun n ↦ ⟪v, x n⟫_ℝ - ⟪v, y⟫_ℝ) atTop (𝓝 (⟪v, y⟫_ℝ - ⟪v, y⟫_ℝ)) := by
    exact hEval'.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ⟪v, y⟫_ℝ) atTop (𝓝 ⟪v, y⟫_ℝ))
  simpa [inner_sub_right, real_inner_comm] using hsub

omit [CompleteSpace H] in
private lemma residual_difference_norm_sq_le_two_inner
    {D : Set H} {T : D → H} (hT : LipschitzWith 1 T) {xSeq : ℕ → D} {x : D} :
    ∀ n,
      ‖(((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))‖ ^ 2 ≤
        2 * ⟪(xSeq n : H) - x, (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))⟫_ℝ := by
  intro n
  have hnonexp : ‖T (xSeq n) - T x‖ ≤ ‖(xSeq n : H) - x‖ := by
    simpa [dist_eq_norm, Subtype.dist_eq] using hT.dist_le_mul (xSeq n) x
  have hsq : ‖T (xSeq n) - T x‖ ^ 2 ≤ ‖(xSeq n : H) - x‖ ^ 2 := by
    nlinarith [hnonexp, norm_nonneg (T (xSeq n) - T x), norm_nonneg ((xSeq n : H) - x)]
  have hrewrite :
      T (xSeq n) - T x = ((xSeq n : H) - x) - (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x)) := by
    abel
  have hsq' :
      ‖((xSeq n : H) - x) - (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))‖ ^ 2 ≤
        ‖(xSeq n : H) - x‖ ^ 2 := by
    simpa [hrewrite] using hsq
  have hexp :=
    norm_sub_sq_real ((xSeq n : H) - x) (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))
  nlinarith [hsq', hexp]

private lemma residual_difference_inner_tendsto_zero
    {D : Set H} {T : D → H} {xSeq : ℕ → D} {x : D} {u : H}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n : H)) atTop
      (𝓝 (toWeakSpace ℝ H (x : H))))
    (hu : Tendsto (fun n ↦ (xSeq n : H) - T (xSeq n)) atTop (𝓝 u)) :
    Tendsto
      (fun n ↦ ⟪(xSeq n : H) - x, (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))⟫_ℝ)
      atTop (𝓝 0) := by
  have hbounded : Bornology.IsBounded (Set.range fun n ↦ (xSeq n : H)) :=
    bounded_range_of_tendsto_toWeakSpace hx
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0 + ‖(x : H)‖
  have hC : ∀ n, ‖(xSeq n : H) - x‖ ≤ C := by
    intro n
    calc
      ‖(xSeq n : H) - x‖ ≤ ‖(xSeq n : H)‖ + ‖(x : H)‖ := norm_sub_le _ _
      _ ≤ max C₀ 0 + ‖(x : H)‖ := by
        exact add_le_add (le_trans (hC₀ _ (Set.mem_range_self n)) (le_max_left _ _)) le_rfl
      _ = C := rfl
  have hfixed : Tendsto (fun n ↦ ⟪(xSeq n : H) - x, u - ((x : H) - T x)⟫_ℝ) atTop (𝓝 0) := by
    simpa only [sub_eq_add_neg] using tendsto_inner_sub_right_zero hx
  have hdiff : Tendsto (fun n ↦ (((xSeq n : H) - T (xSeq n)) - u)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n ↦ (((xSeq n : H) - T (xSeq n)) - u)) atTop (𝓝 (u - u)) := by
      exact hu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ u) atTop (𝓝 u))
    simpa using hsub
  have hnorm_diff : Tendsto (fun n ↦ ‖((xSeq n : H) - T (xSeq n)) - u‖) atTop (𝓝 0) := by
    simpa using hdiff.norm
  have hmul : Tendsto (fun n ↦ C * ‖((xSeq n : H) - T (xSeq n)) - u‖) atTop (𝓝 0) := by
    simpa using hnorm_diff.const_mul C
  have hsecond_abs :
      Tendsto (fun n ↦ |⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ|) atTop
        (𝓝 0) := by
    refine squeeze_zero' (f := fun n ↦ |⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ|)
      (g := fun n ↦ C * ‖((xSeq n : H) - T (xSeq n)) - u‖)
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards with n
      exact le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    · simpa using hmul
  have hsecond :
      Tendsto (fun n ↦ ⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ) atTop
        (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp] using hsecond_abs
  have hsplit :
      (fun n ↦ ⟪(xSeq n : H) - x, (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))⟫_ℝ) =
        fun n ↦
          ⟪(xSeq n : H) - x, u - ((x : H) - T x)⟫_ℝ +
            ⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ := by
    funext n
    rw [show (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x)) =
        (u - ((x : H) - T x)) + (((xSeq n : H) - T (xSeq n)) - u) by abel,
      inner_add_right]
  rw [hsplit]
  simpa using hfixed.add hsecond

/-- Canonical residual form of Browder demiclosedness: on the subtype domain `D`, a nonexpansive
map has demiclosed residual map. -/
theorem demiclosed_residual_of_nonexpansive
    {D : Set H} {T : D → H} (hT : LipschitzWith 1 T) :
    Demiclosed D (fun x ↦ (x : H) - T x) := by
  intro u xₙ x hweak hu
  have hsq_left :
      Tendsto (fun n ↦ ‖(((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))‖ ^ 2) atTop
        (𝓝 (‖u - ((x : H) - T x)‖ ^ 2)) := by
    have hdiff : Tendsto (fun n ↦ (((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))) atTop
        (𝓝 (u - ((x : H) - T x))) := by
      exact hu.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (x : H) - T x) atTop (𝓝 ((x : H) - T x)))
    simpa using hdiff.norm.pow 2
  have hinner_zero :
      Tendsto
        (fun n ↦ ⟪(xₙ n : H) - x, (((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))⟫_ℝ)
        atTop (𝓝 0) :=
    residual_difference_inner_tendsto_zero hweak hu
  have hsq_right :
      Tendsto
        (fun n ↦ 2 * ⟪(xₙ n : H) - x, (((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))⟫_ℝ)
        atTop (𝓝 0) := by
    simpa using hinner_zero.const_mul 2
  have hnonpos : ‖u - ((x : H) - T x)‖ ^ 2 ≤ 0 := by
    exact le_of_tendsto_of_tendsto hsq_left hsq_right <|
      Eventually.of_forall (residual_difference_norm_sq_le_two_inner hT)
  have hsq_zero : ‖u - ((x : H) - T x)‖ ^ 2 = 0 := by
    exact le_antisymm hnonpos (sq_nonneg ‖u - ((x : H) - T x)‖)
  have hnorm_zero : ‖u - ((x : H) - T x)‖ = 0 := eq_zero_of_pow_eq_zero hsq_zero
  have hzero : u - ((x : H) - T x) = 0 := norm_eq_zero.mp hnorm_zero
  exact (sub_eq_zero.mp hzero).symm

/-- Theorem 4.27: Browder's demiclosedness principle says that if `D` is weakly sequentially
closed in a real Hilbert space and `T` is nonexpansive on `D`, then weak convergence of a sequence
in `D` together with norm convergence of the residuals `xₙ - T xₙ` forces the limit residual to be
`x - T x`. -/
-- Proof sketch: use weak sequential closedness to show that the weak limit `x` belongs to `D`.
-- Then expand `‖x - T x - u‖²` around the sequence terms, estimate the `‖T (xSeq n) - T x‖²`
-- term by nonexpansiveness, and pass to the limit using norm convergence of the residuals and weak
-- convergence of `xSeq` to make the inner-product error terms vanish.
theorem browder_demiclosedness_principle
    {D : Set H} (hD : IsSeqClosed ((toWeakSpace ℝ H) '' D))
    {T : H → H} (hT : LipschitzOnWith 1 T D) {xSeq : ℕ → H} (hxSeq : ∀ n, xSeq n ∈ D)
    {x u : H}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hu : Tendsto (fun n ↦ xSeq n - T (xSeq n)) atTop (𝓝 u)) :
    x - T x = u := by
  have hxD : x ∈ D := by
    have hxWeakMem : ∀ n, toWeakSpace ℝ H (xSeq n) ∈ ((toWeakSpace ℝ H) '' D) := by
      intro n
      exact ⟨xSeq n, hxSeq n, rfl⟩
    rcases hD hxWeakMem hx with ⟨y, hyD, hyEq⟩
    have hyx : y = x := (toWeakSpace ℝ H).injective hyEq
    simpa [hyx] using hyD
  let T' : D → H := fun z ↦ T z
  have hT' : LipschitzWith 1 T' := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro y z
    simpa [T', Subtype.dist_eq] using hT.dist_le_mul y y.property z z.property
  let xSeq' : ℕ → D := fun n ↦ ⟨xSeq n, hxSeq n⟩
  let xD : D := ⟨x, hxD⟩
  have hx' :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq' n : H)) atTop (𝓝 (toWeakSpace ℝ H (xD : H))) := by
    simpa [xSeq', xD] using hx
  have hu' : Tendsto (fun n ↦ (xSeq' n : H) - T' (xSeq' n)) atTop (𝓝 u) := by
    simpa [xSeq', T'] using hu
  simpa [T', xD] using (demiclosed_residual_of_nonexpansive hT') u hx' hu'
