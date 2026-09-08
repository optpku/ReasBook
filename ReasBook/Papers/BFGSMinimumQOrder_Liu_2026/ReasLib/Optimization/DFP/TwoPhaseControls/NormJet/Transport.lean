module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder.Transport
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform
public import ReasLib.Analysis.Asymptotics.UniformRemainder.ContinuousLinearMap

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.NormJet

/-!
# Generic norm-jet transport

This companion contains coefficient-free interfaces for transporting remainder information
to the scalar norm observables used by the two-phase consumers.  The statements deliberately
separate the analytic transport from the concrete slow-graph coefficients.
-/

/-- A lower bound on the sum of two norms turns a squared-norm remainder into a norm
remainder with the reciprocal lower-bound constant. -/
theorem isBigO_norm_sub_of_sq_norm_sub
    {α F : Type*} [NormedAddCommGroup F]
    {l : Filter α} {u v : α → F} {r : α → ℝ}
    (hSq : (fun x ↦ ‖u x‖ ^ 2 - ‖v x‖ ^ 2) =O[l] r)
    {c : ℝ} (hc : 0 < c)
    (hLower : ∀ᶠ x in l, c ≤ ‖u x‖ + ‖v x‖) :
    (fun x ↦ ‖u x‖ - ‖v x‖) =O[l] r := by
  obtain ⟨C, hC, hbound⟩ := hSq.exists_nonneg
  have hbound' := hbound.bound
  apply Asymptotics.IsBigO.of_bound (C / c)
  filter_upwards [hLower, hbound'] with x hxLower hxBound
  have hidentity :
      (‖u x‖ - ‖v x‖) * (‖u x‖ + ‖v x‖) =
        ‖u x‖ ^ 2 - ‖v x‖ ^ 2 := by
    ring
  have habsIdentity :
      |‖u x‖ - ‖v x‖| * (‖u x‖ + ‖v x‖) =
        |‖u x‖ ^ 2 - ‖v x‖ ^ 2| := by
    have hsum : 0 ≤ ‖u x‖ + ‖v x‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [← abs_of_nonneg hsum, ← abs_mul, hidentity]
  have hscaled :
      |‖u x‖ - ‖v x‖| * c ≤
        |‖u x‖ ^ 2 - ‖v x‖ ^ 2| := by
    calc
      |‖u x‖ - ‖v x‖| * c ≤
          |‖u x‖ - ‖v x‖| * (‖u x‖ + ‖v x‖) := by
        exact mul_le_mul_of_nonneg_left hxLower (abs_nonneg _)
      _ = |‖u x‖ ^ 2 - ‖v x‖ ^ 2| := habsIdentity
  calc
    ‖‖u x‖ - ‖v x‖‖ = |‖u x‖ - ‖v x‖| := Real.norm_eq_abs _
    _ ≤ |‖u x‖ ^ 2 - ‖v x‖ ^ 2| / c :=
      (le_div_iff₀ hc).2 hscaled
    _ = ‖‖u x‖ ^ 2 - ‖v x‖ ^ 2‖ / c := by
      rw [Real.norm_eq_abs]
    _ ≤ (C * ‖r x‖) / c := by
      exact div_le_div_of_nonneg_right hxBound (le_of_lt hc)
    _ = (C / c) * ‖r x‖ := by ring

/-- Continuous-linear postcomposition transports a uniform finite-jet family, including
its coefficient bounds and every-positive-coefficient Peano remainders. -/
theorem FiniteTaylorJet.IsUniformOn.postcompContinuousLinearMap
    {Θ E F G : Type*}
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} {f : Θ → E → F}
    {J : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ}
    (hJ : FiniteTaylorJet.IsUniformOn f J a K)
    (L : F →L[ℝ] G) :
    FiniteTaylorJet.IsUniformOn
      (fun θ z ↦ L (f θ z))
    (fun θ ↦ FiniteTaylorJet.postcompContinuousLinearMap L (J θ)) a K := by
  rw [FiniteTaylorJet.IsUniformOn.spec]
  constructor
  · intro n
    obtain ⟨B, hB, hbound⟩ := hJ.boundedCoeff n
    refine ⟨‖L‖ * B, mul_nonneg (norm_nonneg L) hB, ?_⟩
    intro θ hθ
    rw [FiniteTaylorJet.coeff_postcompContinuousLinearMap]
    calc
      ‖L.compContinuousMultilinearMap ((J θ).coeff n)‖ ≤
          ‖L‖ * ‖(J θ).coeff n‖ := by
            exact L.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖L‖ * B :=
        mul_le_mul_of_nonneg_left (hbound θ hθ) (norm_nonneg L)
  · intro C hC
    let C' := C / (‖L‖ + 1)
    have hC' : 0 < C' := by
      dsimp only [C']
      have hdenPos : 0 < ‖L‖ + 1 := by
        positivity
      exact div_pos hC hdenPos
    have hrem := hJ.remainder C' hC'
    have hpost := FiniteTaylorJet.IsUniformRemainderOn.postcompContinuousLinearMap hrem L
    have hscale : ‖L‖ * C' ≤ C := by
      dsimp only [C']
      have hden : 0 < ‖L‖ + 1 := by positivity
      have hfrac : ‖L‖ / (‖L‖ + 1) ≤ 1 := by
        apply (div_le_iff₀ hden).2
        linarith
      calc
        ‖L‖ * (C / (‖L‖ + 1)) = C * (‖L‖ / (‖L‖ + 1)) := by ring
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hfrac hC.le
        _ = C := by ring
    obtain ⟨δ, hδ, hbound⟩ :=
      FiniteTaylorJet.IsUniformRemainderOn.bound hpost
    refine (FiniteTaylorJet.IsUniformRemainderOn.spec
      (fun θ z ↦ L (f θ z))
      (fun θ ↦ FiniteTaylorJet.postcompContinuousLinearMap L (J θ))
      a K C (m : ℝ)).mpr ⟨δ, hδ, ?_⟩
    intro θ hθ h hh
    calc
      ‖((FiniteTaylorJet.postcompContinuousLinearMap L (J θ)).remainder
          (fun z ↦ L (f θ z)) a h)‖ ≤
          (‖L‖ * C') * ‖h‖ ^ (m : ℝ) := hbound θ hθ h hh
      _ ≤ C * ‖h‖ ^ (m : ℝ) :=
        mul_le_mul_of_nonneg_right hscale
          (Real.rpow_nonneg (norm_nonneg h) (m : ℝ))

end DFP.TwoLeg.NormJet
