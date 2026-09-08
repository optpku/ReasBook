module

public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_12_Complete_space_of_small_local_graphs
public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_13_Local_cutoff_preserving_the_fixed_point_jet
public import ReasLib.Analysis.Calculus.LocalCutoff.CenterProjection

public section

open scoped Manifold NNReal

universe u

namespace LocalCutoff.CenterProjection

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}
variable (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
  (N : ℝ × X → ℝ × X) (lower upper : ℝ≥0) (forwardBound : ℕ → ℝ≥0)
  (hν : 2 ≤ ν)
  (h_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
    ContDiff ℝ ν (map χ ρ L N ζ))
  (h_lower_pos : 0 < lower)
  (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
    (lower : ℝ) ≤ deriv (map χ ρ L N ζ) u)
  (h_upper : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
    ‖deriv (map χ ρ L N ζ) u‖ ≤ (upper : ℝ))
  (h_forward : ∀ j, 2 ≤ j → j ≤ ν →
    ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      ‖iteratedDeriv j (map χ ρ L N ζ) u‖ ≤ (forwardBound j : ℝ))
  (ζ : SmallLipschitzGraph X radius slope) (u : ℝ)

#check (map_apply χ ρ L N ζ u :
  map χ ρ L N ζ u = (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).1)

#check (inverse_def χ ρ L N ζ :
  inverse χ ρ L N ζ = Function.invFun (map χ ρ L N ζ))

#check (Real.bijective_of_pos_le_deriv
  ((h_smooth ζ).differentiable
    (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν))))
  h_lower_pos (h_lower ζ) : Function.Bijective (map χ ρ L N ζ))

#check (Real.contDiff_invFun_of_pos_le_deriv
  (h_smooth ζ) ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν)
  h_lower_pos (h_lower ζ) :
    ContDiff ℝ ν (Function.invFun (map χ ρ L N ζ)))

/- Infrastructure I.14 (Quantitative inverse for the center projection) (1): every center
projection with the stated uniform smoothness and positive-derivative bounds determines an
explicit `C^ν` diffeomorphism of `ℝ`. -/
#check (Real.diffeomorphOfPosLEDeriv (map χ ρ L N ζ) ν lower
  (h_smooth ζ) ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν)
  h_lower_pos (h_lower ζ) : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ν)

#check (Real.diffeomorphOfPosLEDeriv_apply (map χ ρ L N ζ) ν lower
  (h_smooth ζ) ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν)
  h_lower_pos (h_lower ζ) u :
    Real.diffeomorphOfPosLEDeriv (map χ ρ L N ζ) ν lower
      (h_smooth ζ) ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν)
      h_lower_pos (h_lower ζ) u = map χ ρ L N ζ u)

#check (Real.diffeomorphOfPosLEDeriv_symm_apply (map χ ρ L N ζ) ν lower
  (h_smooth ζ) ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν)
  h_lower_pos (h_lower ζ) u :
    (Real.diffeomorphOfPosLEDeriv (map χ ρ L N ζ) ν lower
      (h_smooth ζ) ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν)
      h_lower_pos (h_lower ζ)).symm u = Function.invFun (map χ ρ L N ζ) u)

/- Infrastructure I.14 (Quantitative inverse for the center projection) (2): every center
projection is strictly increasing under the common positive-derivative bound. -/
#check (Real.strictMono_of_pos_le_deriv
  ((h_smooth ζ).differentiable
    (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν))))
  h_lower_pos (h_lower ζ) : StrictMono (map χ ρ L N ζ))

/- Infrastructure I.14 (Quantitative inverse for the center projection) (3): a common upper
derivative bound gives a common global Lipschitz constant. -/
#check (lipschitzWith_of_nnnorm_deriv_le
  ((h_smooth ζ).differentiable
    (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν))))
  (fun x ↦ NNReal.coe_le_coe.mp (h_upper ζ x)) :
    LipschitzWith upper (map χ ρ L N ζ))

/- Infrastructure I.14 (Quantitative inverse for the center projection) (4): the common positive
lower derivative bound gives reciprocal antilipschitz and inverse Lipschitz constants. -/
#check (Real.antilipschitzWith_inv_of_pos_le_deriv
  ((h_smooth ζ).differentiable
    (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν))))
  h_lower_pos (h_lower ζ) : AntilipschitzWith lower⁻¹ (map χ ρ L N ζ))

#check (Real.lipschitzWith_invFun_of_pos_le_deriv
  ((h_smooth ζ).differentiable
    (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν))))
  h_lower_pos (h_lower ζ) :
    LipschitzWith lower⁻¹ (Function.invFun (map χ ρ L N ζ)))

/- Infrastructure I.14 (Quantitative inverse for the center projection) (5): compact support of
the cutoff yields one interval outside which every center projection is the identity. -/
#check (eq_id_of_abs_ge (radius := radius) (slope := slope) χ ρ L N :
  ρ ≠ 0 → HasCompactSupport χ →
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (η : SmallLipschitzGraph X radius slope) v,
      R ≤ |v| → map χ ρ L N η v = v)

/- Infrastructure I.14 (Quantitative inverse for the center projection) (6): uniform bounds on
the positive-order derivatives of the forward maps give common bounds on inverse derivatives
through order `ν`. -/
#check (Real.exists_uniform_iteratedDeriv_invFun_bound
  ((Nat.succ_le_succ (Nat.zero_le 1)).trans hν) h_smooth h_lower_pos h_lower h_forward :
    ∃ inverseBound : ℕ → ℝ≥0, inverseBound 1 = lower⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ ν → ∀ (η : SmallLipschitzGraph X radius slope) v,
        ‖iteratedDeriv j (Function.invFun (map χ ρ L N η)) v‖ ≤
          (inverseBound j : ℝ))

end LocalCutoff.CenterProjection
