/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped LevelSetNotation
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

section

variable {F : E₁ → E₂} {φ : E₂ → ℝ} {J : E₁ → E₁ →L[ℝ] E₂}

local notation "f" => meritFunctionReformulation F φ

-- Proof sketch: argue by contradiction. If `step x` left the level set, then because the whole
-- level set `𝓛(f(x))` lies in `interior 𝓕`, the segment from `x` to `step x` would meet the
-- boundary of `𝓕`. At that boundary point, use the quadratic upper-model estimate together with
-- convexity of the local-model slice `ψ[F; φ; J](x; ·)` to compare the true objective with the
-- modified Gauss--Newton model. The inequality `L ≤ M` and the basic model-gap estimate from
-- Lemma 4.4.2 then force a contradiction.
/-- Lemma 4.4.4: if the local-model slice `ψ[F; φ; J](x; ·)` is convex, the textbook level set
`𝓛(f(x))` of the continuous merit reformulation is contained in `interior 𝓕`, and
`M ≥ L ≥ 0`, then the modified Gauss--Newton iterate `V_M(x)` belongs to the same level set. -/
theorem modifiedGaussNewton_step_mem_levelSet_of_levelSet_subset_interior
    {𝓕 : Set E₁} {L : NNReal} {M : ℝ}
    (step : ModifiedGaussNewtonStep (ψ[F; φ; J]) 𝓕 M)
    (x : 𝓕)
    (hcont : Continuous f)
    (hconv : ConvexOn ℝ Set.univ (ψ[F; φ; J] x))
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓕 →
        f y ≤
          quadraticallyRegularizedObjective
            (ψ[F; φ; J] x)
            (L : ℝ) x y)
    (hlevel : (𝓛[f]((f x)) : Set E₁) ⊆ interior 𝓕)
    (hLM : (L : ℝ) ≤ M) :
    step x ∈ 𝓛[f]((f x)) := by
  let x0 : E₁ := x
  have hconv0 : ConvexOn ℝ Set.univ (ψ[F; φ; J] x0) := by
    simpa [x0] using hconv
  have hcont0 : Continuous (meritFunctionReformulation F φ) := hcont
  have hupper0 :
      ∀ ⦃y : E₁⦄, y ∈ 𝓕 →
        meritFunctionReformulation F φ y ≤
          quadraticallyRegularizedObjective
            (ψ[F; φ; J] x0)
            (L : ℝ) x0 y := by
    simpa [x0] using hupper
  have hlevel0 : (𝓛[f]((f x0)) : Set E₁) ⊆ interior 𝓕 := by
    simpa [x0] using hlevel
  let y := step x
  let z : ℝ → E₁ := fun t ↦ x0 + t • (y - x0)
  let qL : E₁ → ℝ :=
    quadraticallyRegularizedObjective (ψ[F; φ; J] x0) (L : ℝ) x0
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  have hy_min :
      IsMinOn (quadraticallyRegularizedObjective (ψ[F; φ; J] x0) M x0) Set.univ y := by
    simpa [y] using step.isMinOn_apply x
  have hqMy_le : quadraticallyRegularizedObjective (ψ[F; φ; J] x0) M x0 y ≤ f x0 := by
    simpa [quadraticallyRegularizedObjective_apply, x0, y] using (isMinOn_univ_iff.mp hy_min) x0
  have hqLy_le : qL y ≤ f x0 := by
    have hqL_le_qM :
        qL y ≤ quadraticallyRegularizedObjective (ψ[F; φ; J] x0) M x0 y := by
      simp [qL, quadraticallyRegularizedObjective_apply]
      nlinarith [sq_nonneg ‖y - x0‖, hLM]
    exact hqL_le_qM.trans hqMy_le
  have hz_sub (t : ℝ) : z t - x0 = t • (y - x0) := by
    simp [z]
  have hpsi_le (t : ℝ) (ht : t ∈ I) :
      ψ[F; φ; J] x0 (z t) ≤ (1 - t) * ψ[F; φ; J] x0 x0 + t * ψ[F; φ; J] x0 y := by
    have hconv_t :
        ψ[F; φ; J] x0 (AffineMap.lineMap x0 y t) ≤
          (1 - t) * ψ[F; φ; J] x0 x0 + t * ψ[F; φ; J] x0 y := by
      simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using
        hconv0.2 (show x0 ∈ Set.univ by simp) (show y ∈ Set.univ by simp)
          (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hsegment : z t = AffineMap.lineMap x0 y t := by
      rw [AffineMap.lineMap_apply_module']
      ac_rfl
    simpa [hsegment] using hconv_t
  have hqL_le (t : ℝ) (ht : t ∈ I) : qL (z t) ≤ f x0 := by
    have ht_sq_le : t ^ (2 : ℕ) ≤ t := by
      nlinarith [ht.1, ht.2]
    have hnorm :
        ‖z t - x0‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖y - x0‖ ^ (2 : ℕ) := by
      rw [hz_sub, norm_smul, Real.norm_of_nonneg ht.1, mul_pow]
    have hqLy' :
        ψ[F; φ; J] x0 y + ((L : ℝ) / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ) ≤ f x0 := by
      simpa [qL, quadraticallyRegularizedObjective_apply, x0] using hqLy_le
    have hxx : ψ[F; φ; J] x0 x0 = f x0 := by
      simp [meritFunctionReformulation_apply]
    let c : ℝ := ((L : ℝ) / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have hpenalty_le :
        ((L : ℝ) / 2 : ℝ) * (t ^ (2 : ℕ) * ‖y - x0‖ ^ (2 : ℕ)) ≤
          t * (((L : ℝ) / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) := by
      have hct : c * t ^ (2 : ℕ) ≤ c * t :=
        mul_le_mul_of_nonneg_left ht_sq_le hc_nonneg
      simpa [c, mul_assoc, mul_left_comm, mul_comm] using hct
    change ψ[F; φ; J] x0 (z t) + ((L : ℝ) / 2 : ℝ) * ‖z t - x0‖ ^ (2 : ℕ) ≤ f x0
    rw [hnorm]
    have hpsi := hpsi_le t ht
    nlinarith
  have hlevel_closed : IsClosed (𝓛[f]((f x0)) : Set E₁) := by
    simpa [levelSet_eq_setOf] using isClosed_Iic.preimage hcont0
  let segment : I → E₁ := fun t ↦ z t
  have hsegment_cont : Continuous segment := by
    exact (continuous_const.add (continuous_subtype_val.smul continuous_const))
  let U : Set I := segment ⁻¹' interior 𝓕
  have hU_open : IsOpen U := isOpen_interior.preimage hsegment_cont
  have hU_eq :
      U = segment ⁻¹' (𝓛[f]((f x0)) : Set E₁) := by
    ext t
    constructor
    · intro htU
      have ht𝓕 : segment t ∈ 𝓕 := interior_subset htU
      have ht_upper :
          f (segment t) ≤ qL (segment t) :=
        hupper0 ht𝓕
      have ht_level : segment t ∈ 𝓛[f]((f x0)) := by
        simpa [segment] using ht_upper.trans (hqL_le t t.2)
      exact ht_level
    · intro ht_level
      exact hlevel0 ht_level
  have hU_closed : IsClosed U := by
    rw [hU_eq]
    exact hlevel_closed.preimage hsegment_cont
  have hU_clopen : IsClopen U := ⟨hU_closed, hU_open⟩
  letI : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc
  have h0 : (⟨0, by constructor <;> norm_num⟩ : I) ∈ U := by
    have hx0_level : x0 ∈ 𝓛[f]((f x0)) := by
      simp [x0]
    simpa [U, segment, z, x0] using hlevel0 hx0_level
  have hU_univ : U = Set.univ := hU_clopen.eq_univ ⟨_, h0⟩
  have h1U : (⟨1, by constructor <;> norm_num⟩ : I) ∈ U := by
    simp [hU_univ]
  have hy𝓕 : y ∈ 𝓕 := by
    have : segment ⟨1, by constructor <;> norm_num⟩ ∈ interior 𝓕 := h1U
    simpa [segment, z, y, x0] using interior_subset this
  have hy_upper : f y ≤ qL y := hupper0 hy𝓕
  simpa [y] using hy_upper.trans hqLy_le

end
