/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Example 5.29: an averaged linear map on `Set.univ` is nonexpansive on the ambient
space. -/
private theorem ambient_lipschitzWith_one_of_averaged_on_univ
    {T : H →L[ℝ] H} {α : ℝ}
    (havg : AveragedWith α (fun x : (Set.univ : Set H) ↦ (T (x : H) : H))) :
    LipschitzWith 1 (T : H → H) := by
  rcases averagedWith_iff.mp havg with ⟨hα, R, hR, hT_eq⟩
  have hα_nonneg : 0 ≤ α := hα.1.le
  have h_one_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hRxy :
      ‖R ⟨x, Set.mem_univ x⟩ - R ⟨y, Set.mem_univ y⟩‖ ≤ ‖x - y‖ := by
    -- The averaged companion already satisfies the required nonexpansive estimate.
    simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using
      hR.dist_le_mul ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩
  have hx :
      T x = (1 - α) • x + α • R ⟨x, Set.mem_univ x⟩ := by
    -- Evaluate the averaged decomposition at `x`.
    simpa using congrFun hT_eq ⟨x, Set.mem_univ x⟩
  have hy :
      T y = (1 - α) • y + α • R ⟨y, Set.mem_univ y⟩ := by
    -- Evaluate the averaged decomposition at `y`.
    simpa using congrFun hT_eq ⟨y, Set.mem_univ y⟩
  have hxy :
      T x - T y =
        (1 - α) • (x - y) + α • (R ⟨x, Set.mem_univ x⟩ - R ⟨y, Set.mem_univ y⟩) := by
    -- Subtract the two affine decompositions and collect the residual terms.
    calc
      T x - T y =
          ((1 - α) • x + α • R ⟨x, Set.mem_univ x⟩) -
            ((1 - α) • y + α • R ⟨y, Set.mem_univ y⟩) := by rw [hx, hy]
      _ =
          (1 - α) • (x - y) + α • (R ⟨x, Set.mem_univ x⟩ - R ⟨y, Set.mem_univ y⟩) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- The triangle inequality collapses the averaged combination back to `‖x - y‖`.
  simpa [dist_eq_norm, one_mul] using
    calc
      ‖T x - T y‖ =
          ‖(1 - α) • (x - y) + α • (R ⟨x, Set.mem_univ x⟩ - R ⟨y, Set.mem_univ y⟩)‖ := by
            rw [hxy]
      _ ≤ ‖(1 - α) • (x - y)‖ + ‖α • (R ⟨x, Set.mem_univ x⟩ - R ⟨y, Set.mem_univ y⟩)‖ :=
            norm_add_le _ _
      _ = (1 - α) * ‖x - y‖ + α * ‖R ⟨x, Set.mem_univ x⟩ - R ⟨y, Set.mem_univ y⟩‖ := by
            rw [norm_smul, norm_smul]
            simp [Real.norm_eq_abs, abs_of_nonneg h_one_sub_nonneg, abs_of_nonneg hα_nonneg]
      _ ≤ (1 - α) * ‖x - y‖ + α * ‖x - y‖ := by
            nlinarith [hRxy, norm_nonneg (x - y)]
      _ = ‖x - y‖ := by ring

omit [CompleteSpace H] in
/-- Helper for Example 5.29: relaxation parameter `1` turns the relaxed iteration into the usual
Picard iterates. -/
private theorem relaxed_one_eq_iterates {T : H → H} (x₀ : H) :
    relaxedOperatorIteration (fun _ ↦ T) (fun _ ↦ (1 : ℝ)) x₀ = fun n ↦ (T^[n]) x₀ := by
  funext n
  induction n with
  | zero =>
      -- Both recursions start at the same initial point.
      simp [relaxedOperatorIteration]
  | succ n ih =>
      -- The relaxed step with weight `1` is exactly one application of `T`.
      rw [relaxedOperatorIteration_succ, ih]
      simp [Function.iterate_succ_apply', sub_eq_add_neg]

omit [CompleteSpace H] in
/-- Helper for Example 5.29: the constant relaxation sequence `λₙ = 1` satisfies the divergence
condition from Proposition 5.16 whenever `α ∈ ]0,1[`. -/
private theorem constant_one_relaxation_divergence {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto
      (fun N ↦ Finset.sum (Finset.range N) (fun _ ↦ (1 : ℝ) * (1 - α * (1 : ℝ))))
      atTop atTop := by
  have hconst_pos : 0 < (1 : ℝ) * (1 - α * (1 : ℝ)) := by
    simpa using sub_pos.mpr hα.2
  -- A positive constant summand makes the partial sums grow like `N`.
  convert Tendsto.const_mul_atTop hconst_pos tendsto_natCast_atTop_atTop using 1
  ext N
  simp
  ring

omit [CompleteSpace H] in
/-- Helper for Example 5.29: the Picard residuals of an averaged bounded linear operator converge
strongly to `0`. -/
private theorem picard_residual_tendsto_zero_of_averaged_linear
    {T : H →L[ℝ] H} {α : ℝ}
    (havg : AveragedWith α (fun x : (Set.univ : Set H) ↦ (T (x : H) : H)))
    (x₀ : H) :
    Tendsto (fun n ↦ (T^[n]) x₀ - (T^[n + 1]) x₀) atTop (𝓝 (0 : H)) := by
  have hα : α ∈ Set.Ioo (0 : ℝ) 1 := AveragedWith.mem_Ioo havg
  have hlam : ∀ n : ℕ, (1 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / α) := by
    intro (n : ℕ)
    constructor
    · norm_num
    · -- The constant relaxation `1` is admissible because `α < 1`.
      exact one_le_one_div hα.1 hα.2.le
  have hfix : (Function.fixedPoints (T : H → H)).Nonempty := by
    refine ⟨0, ?_⟩
    -- A linear map always fixes the origin.
    rw [Function.mem_fixedPoints_iff]
    simp
  have hres :
      Tendsto
        (fun n ↦
          T (relaxedOperatorIteration (fun _ ↦ (T : H → H)) (fun _ ↦ (1 : ℝ)) x₀ n) -
            relaxedOperatorIteration (fun _ ↦ (T : H → H)) (fun _ ↦ (1 : ℝ)) x₀ n)
        atTop (𝓝 (0 : H)) := by
    -- Proposition 5.16(ii) gives asymptotic regularity for the constant-relaxation orbit.
    exact residual_tendsto_zero_of_relaxedOperatorIteration_of_averagedWith
      (hT := havg) (lam := fun _ ↦ (1 : ℝ)) (hlam := hlam)
      hfix (constant_one_relaxation_divergence hα) x₀
  have hres_iter :
      Tendsto
        (fun n ↦ (T^[n + 1]) x₀ - (T^[n]) x₀)
        atTop (𝓝 (0 : H)) := by
    -- Rewrite the relaxed orbit as the Picard orbit of `T`.
    simpa [relaxed_one_eq_iterates (T := T) x₀, Function.iterate_succ_apply'] using hres
  -- Flip the residual orientation to match Proposition 5.28.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hres_iter.neg

-- Proof sketch: choose an averaging constant `α`.  Applying Proposition 5.16(ii) to the constant
-- relaxation `λₙ = 1` gives asymptotic regularity of the Picard orbit.  Since the source hypothesis
-- is `T ∈ B(H)`, `T` is a bounded linear operator; Proposition 5.28 then identifies the strong
-- limit with the orthogonal projection of `x₀` onto the fixed-point subspace.
/-- Example 5.29: if a bounded linear operator on a real Hilbert space is averaged, then its
Picard iterates starting at `x₀` converge strongly to the projection of `x₀` onto
`V = Fix T`. -/
theorem tendsto_iterates_to_starProjection_fixedSubspace_of_averaged
    {T : H →L[ℝ] H}
    (havg : ∃ α : ℝ, AveragedWith α (fun x : (Set.univ : Set H) ↦ (T (x : H) : H)))
    (x₀ : H) :
    Tendsto (fun n ↦ (T^[n]) x₀) atTop
      (𝓝 ((fixedSubspace T).starProjection x₀)) := by
  rcases havg with ⟨α, hαavg⟩
  -- Route correction: the corrected bounded-linear statement matches the textbook route
  -- `Proposition 5.16(ii) + Proposition 5.28` exactly.
  have hT_lipschitz : LipschitzWith 1 (T : H → H) :=
    ambient_lipschitzWith_one_of_averaged_on_univ hαavg
  have hres :
      Tendsto (fun n ↦ (T^[n]) x₀ - (T^[n + 1]) x₀) atTop (𝓝 (0 : H)) :=
    picard_residual_tendsto_zero_of_averaged_linear hαavg x₀
  -- Proposition 5.28 upgrades asymptotic regularity of the Picard orbit to strong convergence to
  -- the orthogonal projection onto `Fix T`.
  exact
    (tendsto_iterates_to_starProjection_fixedSubspace_iff_tendsto_residual_zero_of_nonexpansive
      hT_lipschitz x₀).2 hres

end
