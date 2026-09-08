module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

public section

open Filter
open Asymptotics

universe u v w

namespace ContinuousMultilinearMap

variable {T : Type u} {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `x = O(α)` and a perturbation `y` is both `O(α)` and `O(β)`, then the
change of an `n`-homogeneous diagonal multilinear expression is
`O(α^(n-1) β)`. -/
theorem diagonal_add_sub_isBigO
    {n : ℕ} (A : E [×n]→L[ℝ] F) {l : Filter T}
    {x y : T → E} {α β : T → ℝ}
    (hx : x =O[l] α) (hyα : y =O[l] α) (hyβ : y =O[l] β) :
    (fun t : T =>
      A (fun _ : Fin n => x t + y t) - A (fun _ : Fin n => x t)) =O[l]
        (fun t : T => α t ^ (n - 1) * β t) := by
  let X : T → Fin n → E := fun t _ => x t + y t
  let X₀ : T → Fin n → E := fun t _ => x t
  let M : T → ℝ := fun t => max ‖X t‖ ‖X₀ t‖
  let D : T → ℝ := fun t => ‖X t - X₀ t‖
  have hX : X =O[l] α := by
    rw [isBigO_pi]
    intro i
    simpa only [X] using hx.add hyα
  have hX₀ : X₀ =O[l] α := by
    rw [isBigO_pi]
    intro i
    simpa only [X₀] using hx
  have hDvec : (fun t => X t - X₀ t) =O[l] β := by
    rw [isBigO_pi]
    intro i
    simpa only [X, X₀, Pi.sub_apply, add_sub_cancel_left] using hyβ
  have hM : M =O[l] α := by
    have hsum := hX.norm_left.add hX₀.norm_left
    apply (Filter.Eventually.of_forall fun t => ?_).trans_isBigO hsum
    dsimp only [M]
    have hmax : 0 ≤ max ‖X t‖ ‖X₀ t‖ :=
      (norm_nonneg (X t)).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hmax,
      Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  have hD : D =O[l] β := by
    simpa only [D] using hDvec.norm_left
  have hproduct :
      (fun t => M t ^ (n - 1) * D t) =O[l]
        (fun t => α t ^ (n - 1) * β t) :=
    (hM.pow (n - 1)).mul hD
  have hbound : ∀ t : T,
      ‖A (X t) - A (X₀ t)‖ ≤
        ‖A‖ * Fintype.card (Fin n) * M t ^ (Fintype.card (Fin n) - 1) * D t := by
    intro t
    exact A.norm_image_sub_le (X t) (X₀ t)
  apply (Filter.Eventually.of_forall fun t => ?_).trans_isBigO
    (hproduct.const_mul_left (‖A‖ * n))
  simpa only [X, X₀, M, D, Fintype.card_fin, mul_assoc, Real.norm_eq_abs] using
    (hbound t).trans (le_abs_self _)

end ContinuousMultilinearMap
