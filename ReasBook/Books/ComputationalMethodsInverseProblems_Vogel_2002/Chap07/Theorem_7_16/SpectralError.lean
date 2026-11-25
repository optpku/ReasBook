/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.ExpectedError
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.PSeries
/-!
# The exact TSVD estimation-error decomposition

Orthogonality separates each retained mode's noise from the omitted signal.
Parseval's identity separates the nullspace floor from the full coefficient
series. Under the two algebraic decay laws, the expected squared error is
therefore the nullspace floor plus a power-series tail and a finite power sum.

Only second moments of the retained modes are used. No moment assumption
on the rest of the infinite singular system is needed for these identities.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology BigOperators
namespace TsvdEstimation
variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace H] in
lemma orthonormal_partial_error_sq {v : ℕ → H} (hv : Orthonormal ℝ v)
    (f : H) (ξ : ℕ → ℝ) (m : ℕ) :
    ‖(∑ i ∈ Finset.range m, (inner ℝ (v i) f + ξ i) • v i) - f‖ ^ 2 =
      ‖f‖ ^ 2 - (∑ i ∈ Finset.range m, (inner ℝ (v i) f) ^ 2) +
        ∑ i ∈ Finset.range m, (ξ i) ^ 2 := by
  have hn : ‖∑ i ∈ Finset.range m, (inner ℝ (v i) f + ξ i) • v i‖ ^ 2 =
      ∑ i ∈ Finset.range m, (inner ℝ (v i) f + ξ i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hv.inner_sum]
    simp [pow_two]
  rw [norm_sub_sq_real, hn, sum_inner]
  simp only [real_inner_smul_left]
  have halg : (∑ i ∈ Finset.range m, (inner ℝ (v i) f + ξ i) ^ 2) -
      2 * (∑ i ∈ Finset.range m, (inner ℝ (v i) f + ξ i) * inner ℝ (v i) f) =
      (∑ i ∈ Finset.range m, (ξ i) ^ 2) -
        ∑ i ∈ Finset.range m, (inner ℝ (v i) f) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  linarith

lemma norm_sq_eq_nullspace_add_coefficients {K : H →L[ℝ] F}
    (S : ContinuousLinearMap.SingularSystem K) (hlen : S.length = ⊤) (f : H) :
    ‖f‖ ^ 2 = ‖FilterRegularization.nullspaceComponent K f‖ ^ 2 +
      ∑' i : ℕ, (inner ℝ (S.rightBasis (S.natIndex hlen i) : H) f) ^ 2 := by
  let e : ℕ ≃ S.Index := Equiv.ofBijective (S.natIndex hlen)
    ⟨(S.natIndex_strictMono hlen).injective, by
      intro j
      have hj : (j : ℕ∞) ≠ ⊤ := ne_of_lt (by simpa [hlen] using j.2)
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hj
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩
  let x : K.kerᗮ := K.kerᗮ.orthogonalProjectionOnto f
  have hc (j : S.Index) : inner ℝ x (S.rightBasis j) = inner ℝ f (S.rightBasis j : H) := by
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (S.rightBasis j) f
  have hparseval : (∑' j : S.Index, (inner ℝ (S.rightBasis j : H) f) ^ 2) = ‖x‖ ^ 2 := by
    convert S.rightBasis.tsum_inner_mul_inner x x using 1
    · congr 1
      funext j
      rw [real_inner_comm x (S.rightBasis j), hc, real_inner_comm, pow_two]
    · rw [real_inner_self_eq_norm_sq]
  have hreindex : (∑' i : ℕ, (inner ℝ (S.rightBasis (S.natIndex hlen i) : H) f) ^ 2) =
      ∑' j : S.Index, (inner ℝ (S.rightBasis j : H) f) ^ 2 :=
    e.tsum_eq (fun j ↦ (inner ℝ (S.rightBasis j : H) f) ^ 2)
  rw [hreindex, hparseval, FilterRegularization.nullspaceComponent_eq_starProjection]
  exact K.ker.norm_sq_eq_add_norm_sq_starProjection f

lemma expectedSqErrorObjective_eq_norm_sub_sum_add_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (hlen : ∀ n, (S n).length = ⊤) (f : H) {b c p q σ : ℝ}
    (η : ℕ → Ω → F) (R : ℕ → ℕ → F →L[ℝ] H)
    (hR : IsTsvdReconstructionFamily K S hlen R)
    (hLp : ∀ n, MemLp (η n) 2 μ)
    (hs : ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (hlen n) c p)
    (hf : ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (hlen n) f b q)
    {n m : ℕ}
    (hvar : ∀ i < m, ∫ ω,
      (inner ℝ ((S n).leftBasis ((S n).natIndex (hlen n) i) : F) (η n ω)) ^ 2 ∂μ =
        σ ^ 2 / (n : ℝ)) :
    expectedSqErrorObjective μ K R f η n m =
      ‖f‖ ^ 2 - b * (∑ i ∈ Finset.range m, ((i : ℝ) + 1) ^ (-q)) +
        (σ ^ 2 / ((n : ℝ) * c)) * ∑ i ∈ Finset.range m, ((i : ℝ) + 1) ^ p := by
  let u : ℕ → H := fun i ↦ ((S n).rightBasis ((S n).natIndex (hlen n) i) : H)
  let v : ℕ → F := fun i ↦ ((S n).leftBasis ((S n).natIndex (hlen n) i) : F)
  let s : ℕ → ℝ := fun i ↦ (S n).singularValue ((S n).natIndex (hlen n) i)
  let ξ : ℕ → Ω → ℝ := fun i ω ↦ (1 / s i) * inner ℝ (v i) (η n ω)
  have hu : Orthonormal ℝ u :=
    ((S n).rightBasis.orthonormal.comp_linearIsometry (K n).kerᗮ.subtypeₗᵢ).comp _
      ((S n).natIndex_strictMono (hlen n)).injective
  have hcoeff (i : ℕ) :
      (1 / s i) * inner ℝ (v i) (K n f) = inner ℝ (u i) f := by
    dsimp [u, v, s]
    rw [← ContinuousLinearMap.adjoint_inner_left, (S n).adjoint_map_left, real_inner_smul_left]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    field_simp [(S n).singularValue_pos ((S n).natIndex (hlen n) i) |>.ne']
  have hpoint (ω : Ω) :
      ‖FilterRegularization.estimationError (R n m) (K n) f (η n ω)‖ ^ 2 =
      ‖f‖ ^ 2 - ∑ i ∈ Finset.range m, (inner ℝ (u i) f) ^ 2 +
        ∑ i ∈ Finset.range m, (ξ i ω) ^ 2 := by
    rw [FilterRegularization.estimationError_def, hR n m]
    have heq (i : ℕ) : (1 / s i) * inner ℝ (v i) (K n f + η n ω) =
        inner ℝ (u i) f + ξ i ω := by rw [inner_add_right, mul_add, hcoeff]
    change ‖(∑ i ∈ Finset.range m, ((1 / s i) * inner ℝ (v i) (K n f + η n ω)) • u i) - f‖ ^ 2 = _
    simp_rw [heq]
    exact orthonormal_partial_error_sq hu f (fun i ↦ ξ i ω) m
  have hi (i : ℕ) : Integrable (fun ω ↦ (ξ i ω) ^ 2) μ :=
    (((MemLp.const_inner (v i) (hLp n)).const_mul (1 / s i))).integrable_sq
  have hnoise (i : ℕ) (him : i < m) : ∫ ω, (ξ i ω) ^ 2 ∂μ =
      (σ ^ 2 / ((n : ℝ) * c)) * ((i : ℝ) + 1) ^ p := by
    have hsval : s i ^ 2 = c * ((i : ℝ) + 1) ^ (-p) := by
      simpa [s, Nat.cast_add, Nat.cast_one] using hs n ⟨i + 1, Nat.succ_pos i⟩
    dsimp [ξ]
    simp_rw [mul_pow]
    rw [integral_const_mul, hvar i him, div_pow, one_pow, hsval,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1) p]
    field_simp
  have hsignal (i : ℕ) : (inner ℝ (u i) f) ^ 2 = b * ((i : ℝ) + 1) ^ (-q) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using hf n ⟨i + 1, Nat.succ_pos i⟩
  rw [expectedSqErrorObjective_apply, FilterRegularization.expectedSqEstimationError_def]
  simp_rw [hpoint]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun i _ ↦ hi i)),
    integral_const, probReal_univ, one_smul, integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [hsignal]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i him
  exact hnoise i (Finset.mem_range.1 him)

lemma expectedSqErrorObjective_eq_nullspace_add_tail_add_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (hlen : ∀ n, (S n).length = ⊤) (f : H) {b c p q σ : ℝ} (hq : 1 < q)
    (η : ℕ → Ω → F) (R : ℕ → ℕ → F →L[ℝ] H)
    (hR : IsTsvdReconstructionFamily K S hlen R)
    (hLp : ∀ n, MemLp (η n) 2 μ)
    (hs : ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (hlen n) c p)
    (hf : ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (hlen n) f b q)
    {n m : ℕ}
    (hvar : ∀ i < m, ∫ ω,
      (inner ℝ ((S n).leftBasis ((S n).natIndex (hlen n) i) : F) (η n ω)) ^ 2 ∂μ =
        σ ^ 2 / (n : ℝ)) :
    expectedSqErrorObjective μ K R f η n m =
      ‖FilterRegularization.nullspaceComponent (K n) f‖ ^ 2 +
        (b * (∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-q)) +
        (σ ^ 2 / ((n : ℝ) * c)) * ∑ i ∈ Finset.range m, ((i : ℝ) + 1) ^ p) := by
  have hcoeff (i : ℕ) :
      (inner ℝ ((S n).rightBasis ((S n).natIndex (hlen n) i) : H) f) ^ 2 =
        b * ((i : ℝ) + 1) ^ (-q) := by
    simpa [Nat.cast_add, Nat.cast_one] using hf n ⟨i + 1, Nat.succ_pos i⟩
  have hnorm := norm_sq_eq_nullspace_add_coefficients (S n) (hlen n) f
  simp_rw [hcoeff] at hnorm
  rw [tsum_mul_left] at hnorm
  have hsum : Summable (fun i : ℕ ↦ ((i : ℝ) + 1) ^ (-q)) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      (Real.summable_nat_rpow.2 (by linarith : -q < -1)).comp_injective Nat.succ_injective
  have hsplit := hsum.sum_add_tsum_nat_add m
  simp only [Nat.cast_add] at hsplit
  rw [expectedSqErrorObjective_eq_norm_sub_sum_add_sum μ K S hlen f η R hR hLp hs hf hvar,
    hnorm, ← hsplit]
  push_cast
  ring

end TsvdEstimation
