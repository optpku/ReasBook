module

public import Mathlib.Analysis.Normed.Operator.Basic
public import ReasLib.Analysis.Asymptotics.UniformRemainder

public section

/-!
# Continuous-linear transport of uniform remainders

Uniform remainder bounds are stable under continuous linear maps.  Product projections have
the sharper coefficient-preserving bounds coming directly from the max product norm.
-/

namespace Asymptotics.IsUniformRemainderOn

universe u v w

/-- Applying a continuous linear map transports a uniform remainder bound and scales
its coefficient by the operator norm. -/
theorem continuousLinearMap_apply
    {Θ : Type u} {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : Θ → ℝ → E} {s : Set Θ} {C q : ℝ}
    (L : E →L[ℝ] F) (hR : Asymptotics.IsUniformRemainderOn R s C q) :
    Asymptotics.IsUniformRemainderOn
      (fun θ ε => L (R θ ε)) s (‖L‖ * C) q := by
  refine (isBigOWith_iff (fun θ ε ↦ L (R θ ε)) s (‖L‖ * C) q).mp ?_
  have hR' := (isBigOWith_iff R s C q).mpr hR
  refine IsBigOWith.of_bound ?_
  filter_upwards [hR'.bound] with z hz
  have hRbound : ‖R z.1 z.2‖ ≤ C * |z.2| ^ q := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) q)] using hz
  calc
    ‖L (R z.1 z.2)‖ ≤ ‖L‖ * ‖R z.1 z.2‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (C * |z.2| ^ q) :=
      mul_le_mul_of_nonneg_left hRbound (norm_nonneg L)
    _ = (‖L‖ * C) * |z.2| ^ q := (mul_assoc ‖L‖ C _).symm
    _ = (‖L‖ * C) * ‖|z.2| ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) q)]

/-- Projecting to the first factor preserves a uniform remainder coefficient. -/
theorem fst
    {Θ : Type u} {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {R : Θ → ℝ → E × F} {s : Set Θ} {C q : ℝ}
    (hR : Asymptotics.IsUniformRemainderOn R s C q) :
    Asymptotics.IsUniformRemainderOn (fun θ ε => (R θ ε).1) s C q := by
  refine (isBigOWith_iff (fun θ ε ↦ (R θ ε).1) s C q).mp ?_
  have hR' := (isBigOWith_iff R s C q).mpr hR
  refine IsBigOWith.of_bound ?_
  filter_upwards [hR'.bound] with z hz
  exact (norm_fst_le (R z.1 z.2)).trans hz

/-- Projecting to the second factor preserves a uniform remainder coefficient. -/
theorem snd
    {Θ : Type u} {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {R : Θ → ℝ → E × F} {s : Set Θ} {C q : ℝ}
    (hR : Asymptotics.IsUniformRemainderOn R s C q) :
    Asymptotics.IsUniformRemainderOn (fun θ ε => (R θ ε).2) s C q := by
  refine (isBigOWith_iff (fun θ ε ↦ (R θ ε).2) s C q).mp ?_
  have hR' := (isBigOWith_iff R s C q).mpr hR
  refine IsBigOWith.of_bound ?_
  filter_upwards [hR'.bound] with z hz
  exact (norm_snd_le (R z.1 z.2)).trans hz

end Asymptotics.IsUniformRemainderOn
