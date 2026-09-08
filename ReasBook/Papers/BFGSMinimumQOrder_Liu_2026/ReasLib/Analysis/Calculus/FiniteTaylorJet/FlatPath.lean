module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

public section

open Filter
open scoped Topology

universe u v

namespace FiniteTaylorJet

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Along a path whose first nonconstant terms have degrees three and four, the
four-jet of an analytic map only sees its value and first derivative at the base point. -/
theorem ofFunction_comp_cubic_quartic
    (f : E → F) (a v₃ v₄ : E) (hf : AnalyticAt ℝ f a) :
    ofFunction ℝ 4
        (fun ε : ℝ => f (a + ε ^ 3 • v₃ + ε ^ 4 • v₄)) 0 =
      ofFunction ℝ 4
        (fun ε : ℝ =>
          f a + ε ^ 3 • fderiv ℝ f a v₃ + ε ^ 4 • fderiv ℝ f a v₄) 0 := by
  let k : ℝ → E := fun ε => ε ^ 3 • v₃ + ε ^ 4 • v₄
  obtain ⟨p, hp⟩ := hf
  have hpartial (z : E) :
      p.partialSum 2 z = f a + fderiv ℝ f a z := by
    rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add]
    rw [hp.coeff_zero, hp.fderiv_eq]
    rfl
  have hlinear :
      (fun z : E => f (a + z) - (f a + fderiv ℝ f a z)) =O[𝓝 0]
        (fun z : E => ‖z‖ ^ 2) := by
    simpa only [hpartial] using hp.isBigO_sub_partialSum_pow 2
  let q : ℝ → E := fun ε => v₃ + ε • v₄
  have hq0 : Tendsto q (𝓝 0) (𝓝 v₃) := by
    dsimp only [q]
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
    simpa using tendsto_const_nhds.add (hε.smul_const v₄)
  have hqO : q =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto hq0 one_ne_zero
  have hpowO := Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0)
  have hsmul := hpowO.smul hqO
  have hkO : k =O[𝓝 0] (fun ε : ℝ => ε ^ 3) := by
    refine hsmul.congr' ?_ ?_
    · filter_upwards
      intro ε
      dsimp only [k, q, Pi.smul_apply]
      rw [smul_add, smul_smul]
      congr 1
    · filter_upwards
      intro ε
      simp
  have hk0 : Tendsto k (𝓝 0) (𝓝 0) := by
    apply hkO.trans_tendsto
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
    simpa using hε.pow 3
  have hk2 : (fun ε : ℝ => ‖k ε‖ ^ 2) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 6) := by
    simpa only [← pow_mul, Nat.reduceMul] using hkO.norm_left.pow 2
  have horder : 4 < 6 := by
    norm_num
  have hflatRaw := (hlinear.comp_tendsto hk0).trans hk2 |>.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow horder)
  have hflat :
      (fun ε : ℝ =>
        f (a + ε ^ 3 • v₃ + ε ^ 4 • v₄) -
          (f a + ε ^ 3 • fderiv ℝ f a v₃ + ε ^ 4 • fderiv ℝ f a v₄))
        =o[𝓝 0] (fun ε : ℝ => ε ^ 4) := by
    refine hflatRaw.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards
    intro ε
    dsimp only [k]
    simp only [Function.comp_apply, map_add, map_smul]
    abel
  have hpath : AnalyticAt ℝ (fun ε : ℝ => a + k ε) 0 := by
    dsimp only [k]
    fun_prop
  have hfpath : AnalyticAt ℝ f ((fun ε : ℝ => a + k ε) 0) := by
    simpa [k] using hp.analyticAt
  have hactual : ContDiffAt ℝ 4 (fun ε : ℝ => f (a + k ε)) 0 := by
    have hcomp := hfpath.comp (x := (0 : ℝ)) (f := fun ε : ℝ => a + k ε) hpath
    simpa only [Function.comp_def] using hcomp.contDiffAt
  have hpolynomial : ContDiffAt ℝ 4
      (fun ε : ℝ =>
        f a + ε ^ 3 • fderiv ℝ f a v₃ + ε ^ 4 • fderiv ℝ f a v₄) 0 := by
    fun_prop
  have hflatAt :
      (fun ε : ℝ =>
        f (a + k (0 + ε)) -
          (f a + (0 + ε) ^ 3 • fderiv ℝ f a v₃ +
            (0 + ε) ^ 4 • fderiv ℝ f a v₄))
        =o[𝓝 0] (fun ε : ℝ => ε ^ 4) := by
    simpa only [zero_add, k, add_assoc] using hflat
  have hjet := ofFunction_eq_of_sub_isLittleO hactual hpolynomial hflatAt
  simpa only [k, add_assoc] using hjet

end FiniteTaylorJet
