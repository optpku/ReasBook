module

public import ReasLib.Analysis.Calculus.LocalCutoff.CenterStable
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph

public section

open Filter
open Asymptotics
open scoped NNReal
open scoped Topology

universe u v

namespace LocalInvariantGraph

/-- Helper for Infrastructure I.16a: differentiability at the origin gives an arbitrarily
small normalized linearization error on a neighborhood of the origin. -/
theorem eventually_norm_fderiv_remainder_le_at_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {A : E →L[ℝ] F} (h : HasFDerivAt f A 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 0, ‖f y - f 0 - A y‖ ≤ ε * ‖y‖ := by
  have hlittle : (fun y : E ↦ f y - f 0 - A y) =o[𝓝 0] fun y : E ↦ y := by
    simpa only [zero_add, sub_zero] using
      (hasFDerivAt_iff_isLittleO_nhds_zero (f := f) (f' := A) (x := 0)).mp h
  exact (isLittleO_iff.mp hlittle hε)

/-- Helper for Infrastructure I.16a: the preceding normalized error estimate can be
expressed as a positive-radius ball bound. -/
theorem exists_norm_fderiv_remainder_le_at_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {A : E →L[ℝ] F} (h : HasFDerivAt f A 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, ‖y‖ < δ → ‖f y - f 0 - A y‖ ≤ ε * ‖y‖ := by
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_norm_fderiv_remainder_le_at_zero h hε)
  refine ⟨s, hs, ?_⟩
  intro y hy
  have hmem : y ∈ Metric.ball (0 : E) s := by
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  exact hball hmem

/-- Helper for Infrastructure I.16a: a fixed point of an inverse-coordinate graph
transform satisfies the original parametrized invariant equation after the inverse
is cancelled. -/
theorem fixedPoint_invariant_of_rightInverse
    {E : Type u} [NormedAddCommGroup E]
    {radius slope : ℝ≥0}
    (T : SmallLipschitzGraph E radius slope → SmallLipschitzGraph E radius slope)
    (ζ : SmallLipschitzGraph E radius slope)
    (center : SmallLipschitzGraph E radius slope → ℝ → ℝ)
    (inverse : SmallLipschitzGraph E radius slope → ℝ → ℝ)
    (stable : SmallLipschitzGraph E radius slope → ℝ → E)
    (hfixed : T ζ = ζ)
    (htransform : ∀ u : ℝ,
      T ζ (center ζ u) = stable ζ (inverse ζ (center ζ u)))
    (hinverse : ∀ u : ℝ, inverse ζ (center ζ u) = u) :
    ∀ u : ℝ, ζ (center ζ u) = stable ζ u := by
  intro u
  have hpoint := congrArg (fun η : SmallLipschitzGraph E radius slope ↦ η (center ζ u)) hfixed
  have hvalue := htransform u
  rw [hvalue, hinverse u] at hpoint
  exact hpoint.symm

/-- Helper for Infrastructure I.16a: an invariant graph for a center-stable germ has
zero derivative in the stable direction when the stable block is strictly contractive. -/
theorem tangent_zero_of_centerStable_invariant
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ζ : ℝ → X) (A : ℝ →L[ℝ] X) (F : ℝ × X → ℝ × X)
    (L : X →L[ℝ] X)
    (hζ_zero : ζ 0 = 0)
    (hζ_deriv : HasFDerivAt ζ A 0)
    (hF_zero : F (0, 0) = (0, 0))
    (hF_deriv : HasFDerivAt F (LocalCutoff.centerStable L) (0, 0))
    (h_invariant : (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0]
      (fun u ↦ ζ (F (u, ζ u)).1))
    (hL : ‖L‖ < 1) :
    HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 := by
  let g : ℝ → ℝ × X := fun u ↦ (u, ζ u)
  have hg : HasFDerivAt g
      ((ContinuousLinearMap.id ℝ ℝ).prod A) 0 := by
    simpa only [g, id_eq] using (hasFDerivAt_id (𝕜 := ℝ) 0).prodMk hζ_deriv
  have hF_at_g0 : HasFDerivAt F (LocalCutoff.centerStable L) (g 0) := by
    simpa only [g, hζ_zero, Prod.mk_zero_zero] using hF_deriv
  have hfg : HasFDerivAt (F ∘ g)
      ((LocalCutoff.centerStable L).comp ((ContinuousLinearMap.id ℝ ℝ).prod A)) 0 :=
    hF_at_g0.comp 0 hg
  have hfg_zero : (F ∘ g) 0 = (0, 0) := by
    rw [Function.comp_apply]
    have hg_zero : g 0 = (0, 0) := by simp only [g, hζ_zero, Prod.mk_zero_zero]
    rw [hg_zero, hF_zero]
  have hleft : HasFDerivAt (fun u ↦ (F (g u)).2)
      ((ContinuousLinearMap.snd ℝ ℝ X).comp
        ((LocalCutoff.centerStable L).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod A))) 0 := by
    simpa only [Function.comp_def] using hfg.snd
  have hfirst_zero : (fun u ↦ (F (g u)).1) 0 = 0 := by
    simpa only [Function.comp_def] using congrArg Prod.fst hfg_zero
  have hright : HasFDerivAt (fun u ↦ ζ (F (g u)).1)
      (A.comp ((ContinuousLinearMap.fst ℝ ℝ X).comp
        ((LocalCutoff.centerStable L).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod A)))) 0 := by
    have hζ_at_first : HasFDerivAt ζ A ((fun u ↦ (F (g u)).1) 0) := by
      simpa only [hfirst_zero] using hζ_deriv
    have hcomp := hζ_at_first.comp 0 hfg.fst
    simpa only [Function.comp_def] using hcomp
  have hderiv_eq :
      ((ContinuousLinearMap.snd ℝ ℝ X).comp
        ((LocalCutoff.centerStable L).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod A))) =
      A.comp ((ContinuousLinearMap.fst ℝ ℝ X).comp
        ((LocalCutoff.centerStable L).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod A))) := by
    exact (hleft.congr_of_eventuallyEq h_invariant.symm).unique hright
  have hvector : L (A 1) = A 1 := by
    have heval := congrArg (fun B : ℝ →L[ℝ] X ↦ B 1) hderiv_eq
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.fst, ContinuousLinearMap.snd,
      LocalCutoff.centerStable_apply] using heval
  have hnorm : ‖A 1‖ ≤ ‖L‖ * ‖A 1‖ := by
    calc
      ‖A 1‖ = ‖L (A 1)‖ := congrArg norm hvector.symm
      _ ≤ ‖L‖ * ‖A 1‖ := L.le_opNorm _
  have hA_one : A 1 = 0 := by
    by_contra hne
    have hpos : 0 < ‖A 1‖ := norm_pos_iff.mpr hne
    have hstrict : ‖L‖ * ‖A 1‖ < ‖A 1‖ := by
      simpa only [one_mul] using (mul_lt_mul_of_pos_right hL hpos)
    exact (not_lt_of_ge hnorm) hstrict
  have hA : A = 0 := by
    apply ContinuousLinearMap.ext
    intro t
    have hscalar := A.map_smul t (1 : ℝ)
    simpa only [smul_eq_mul, mul_one, hA_one, smul_zero, zero_apply] using hscalar
  simpa only [hA] using hζ_deriv

end LocalInvariantGraph
