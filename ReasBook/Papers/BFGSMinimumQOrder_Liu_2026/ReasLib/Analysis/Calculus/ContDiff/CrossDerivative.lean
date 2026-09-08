module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public section

open Filter
open scoped Matrix Topology

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the directional derivative in `u` vanishes along the line through `a` in direction `v`,
then the quadratic cross derivative in directions `u, v` vanishes at `a`. -/
theorem ContDiffAt.iteratedFDeriv_two_apply_eq_zero_of_eventually_fderiv_line_eq_zero
    {f : E → F} {a : E} (hf : ContDiffAt ℝ 2 f a) (u v : E)
    (hzero : ∀ᶠ t in 𝓝 (0 : ℝ), fderiv ℝ f (a + t • v) u = 0) :
    iteratedFDeriv ℝ 2 f a ![u, v] = 0 := by
  let D : E → E →L[ℝ] F := fun x => fderiv ℝ f x
  let line : ℝ → E := (fun _ : ℝ => a) + fun t => t • v
  have horder : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hD : DifferentiableAt ℝ D a := by
    exact (hf.fderiv_right (m := 1) horder).differentiableAt one_ne_zero
  have hline : HasDerivAt line v 0 := by
    have ha : HasDerivAt (fun _ : ℝ => a) 0 0 := hasDerivAt_const 0 a
    have hv : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa only [line, zero_add] using ha.add hv
  let ev : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F u
  have hDapp : HasFDerivAt (fun x => D x u) (ev.comp (fderiv ℝ D a)) a := by
    exact ev.hasFDerivAt.comp a hD.hasFDerivAt
  have hchain : HasDerivAt (fun t => D (line t) u)
      ((ev.comp (fderiv ℝ D a)) v) 0 := by
    have hDapp' : HasFDerivAt (fun x => D x u) (ev.comp (fderiv ℝ D a))
        (line 0) := by
      simpa only [line, Pi.add_apply, zero_smul, add_zero] using hDapp
    have hchainRaw := hDapp'.comp_hasDerivAt 0 hline
    change HasDerivAt (fun t => D (line t) u)
      ((ev.comp (fderiv ℝ D a)) v) 0 at hchainRaw
    exact hchainRaw
  have hzero' : ∀ᶠ t in 𝓝 (0 : ℝ), D (line t) u = 0 := by
    simpa only [D, line, Pi.add_apply] using hzero
  have hconst : HasDerivAt (fun _ : ℝ => (0 : F)) 0 0 := hasDerivAt_const 0 0
  have hchainZero : HasDerivAt (fun t => D (line t) u) 0 0 := by
    apply hconst.congr_of_eventuallyEq
    filter_upwards [hzero'] with t ht
    exact ht
  have hvalue : (fderiv ℝ D a) v u = 0 := by
    have hunique := hchain.unique hchainZero
    simpa only [ev, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using hunique
  have hvu : iteratedFDeriv ℝ 2 f a ![v, u] = 0 := by
    rw [iteratedFDeriv_two_apply]
    simpa [D] using hvalue
  have hmin : minSmoothness ℝ (2 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) := by
    norm_num [minSmoothness]
  have hsymm : IsSymmSndFDerivAt ℝ f a := hf.isSymmSndFDerivAt hmin
  exact hsymm.iteratedFDeriv_cons.trans hvu
