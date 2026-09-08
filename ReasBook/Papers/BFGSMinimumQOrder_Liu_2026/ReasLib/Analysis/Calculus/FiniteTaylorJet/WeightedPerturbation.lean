module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Weighted transverse perturbations

Mean-value transport for two nearby parameter paths whose slice derivative
vanishes at a prescribed asymptotic rate.
-/

public section

open Filter
open scoped Convex Topology

universe u v w

namespace FiniteTaylorJet

variable {P : Type u} {F : Type v}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If two parameter paths differ by `O(a)` and the derivative of every fixed-index
slice is uniformly `O(b)` along the segment joining them, then their images differ
by `O(a * b)`.  This is the integral-free mean-value form of weighted transverse
transport. -/
theorem weighted_transverse_isBigO
    {α : Type w} {l : Filter α} {g : α → P → F}
    {u v : α → P} {a b : α → ℝ}
    (huv : (fun ε ↦ u ε - v ε) =O[l] a)
    (hdiff : ∀ᶠ ε in l, ∀ z ∈ segment ℝ (v ε) (u ε),
      DifferentiableAt ℝ (g ε) z)
    (hderiv : ∃ C > 0, ∀ᶠ ε in l,
      ∀ z ∈ segment ℝ (v ε) (u ε),
        ‖fderiv ℝ (g ε) z‖ ≤ C * ‖b ε‖) :
    (fun ε ↦ g ε (u ε) - g ε (v ε)) =O[l]
      (fun ε ↦ a ε * b ε) := by
  obtain ⟨D, hDpos, hD⟩ := (Asymptotics.isBigO_iff').mp huv
  obtain ⟨C, hCpos, hC⟩ := hderiv
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C * D, ?_⟩
  filter_upwards [hdiff, hC, hD] with ε hdiffε hCε hDε
  have hmean :
      ‖g ε (u ε) - g ε (v ε)‖ ≤
        (C * ‖b ε‖) * ‖u ε - v ε‖ := by
    exact (convex_segment (v ε) (u ε)).norm_image_sub_le_of_norm_fderiv_le
      hdiffε hCε (left_mem_segment ℝ (v ε) (u ε))
        (right_mem_segment ℝ (v ε) (u ε))
  calc
    ‖g ε (u ε) - g ε (v ε)‖ ≤
        (C * ‖b ε‖) * ‖u ε - v ε‖ := hmean
    _ ≤ (C * ‖b ε‖) * (D * ‖a ε‖) :=
      mul_le_mul_of_nonneg_left hDε (mul_nonneg hCpos.le (norm_nonneg _))
    _ = (C * D) * ‖a ε * b ε‖ := by
      rw [norm_mul]
      ring

/-- Power-law specialization of `weighted_transverse_isBigO`: an `O(ε^m)`
path perturbation and an `O(ε^k)` slice derivative produce an
`O(ε^(m+k))` image perturbation. -/
theorem weighted_transverse_pow_isBigO
    {g : ℝ × P → F} {u v : ℝ → P} {m k : ℕ}
    (huv : (fun ε ↦ u ε - v ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ m))
    (hdiff : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ z ∈ segment ℝ (v ε) (u ε),
        DifferentiableAt ℝ (fun p : P ↦ g (ε, p)) z)
    (hderiv : ∃ C > 0, ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ z ∈ segment ℝ (v ε) (u ε),
        ‖fderiv ℝ (fun p : P ↦ g (ε, p)) z‖ ≤ C * ‖ε ^ k‖) :
    (fun ε ↦ g (ε, u ε) - g (ε, v ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ (m + k)) := by
  have h := weighted_transverse_isBigO
    (g := fun ε p ↦ g (ε, p))
    (a := fun ε : ℝ ↦ ε ^ m) (b := fun ε : ℝ ↦ ε ^ k)
    huv hdiff hderiv
  simpa only [pow_add] using h

end FiniteTaylorJet
