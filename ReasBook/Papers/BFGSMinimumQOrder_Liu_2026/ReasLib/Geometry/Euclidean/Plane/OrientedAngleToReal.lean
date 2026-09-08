module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.Geometry.Euclidean.Plane.Rotation

/-!
# A real chart for oriented angles in the positive first-coordinate half-plane
-/

public section

noncomputable section

open scoped EuclideanSpace Topology ContDiff

namespace EuclideanPlane

/-- For two planar vectors whose first coordinates are positive, the principal real
representative of their oriented angle is the difference of their arctangent slope coordinates. -/
theorem oangle_toReal_eq_arctan_sub_of_pos (a b c d : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (orientation.oangle
      (!₂[a, b] : EuclideanSpace ℝ (Fin 2))
      (!₂[c, d] : EuclideanSpace ℝ (Fin 2))).toReal =
        Real.arctan (d / c) - Real.arctan (b / a) := by
  let e : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), 0]
  have he : e ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
    change (1 : ℝ) = 0 at hzero
    norm_num at hzero
  have hrightAngle :
      orientation.rotation (Real.pi / 2 : ℝ) e =
        (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) := by
    rw [orientation.rotation_pi_div_two]
    change perp e = _
    rw [perp_apply]
    simp [e]
  have hslope (r : ℝ) :
      e + r • orientation.rotation (Real.pi / 2 : ℝ) e =
        (!₂[(1 : ℝ), r] : EuclideanSpace ℝ (Fin 2)) := by
    rw [hrightAngle]
    ext i
    fin_cases i
    · simp [e]
    · simp [e]
  have hscaledLeft :
      a • (!₂[(1 : ℝ), b / a] : EuclideanSpace ℝ (Fin 2)) =
        (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · simp
    · simp
      field_simp [ha.ne']
  have hscaledRight :
      c • (!₂[(1 : ℝ), d / c] : EuclideanSpace ℝ (Fin 2)) =
        (!₂[c, d] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · simp
    · simp
      field_simp [hc.ne']
  have hfirst : orientation.oangle e
      (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) = Real.arctan (b / a) := by
    rw [← hscaledLeft, orientation.oangle_smul_right_of_pos e _ ha]
    rw [← hslope (b / a)]
    exact orientation.oangle_add_right_smul_rotation_pi_div_two he (b / a)
  have hsecond : orientation.oangle e
      (!₂[c, d] : EuclideanSpace ℝ (Fin 2)) = Real.arctan (d / c) := by
    rw [← hscaledRight, orientation.oangle_smul_right_of_pos e _ hc]
    rw [← hslope (d / c)]
    exact orientation.oangle_add_right_smul_rotation_pi_div_two he (d / c)
  have hleftNe : (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
    change a = 0 at hzero
    exact ha.ne' hzero
  have hrightNe : (!₂[c, d] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
    change c = 0 at hzero
    exact hc.ne' hzero
  have hangle : orientation.oangle
      (!₂[a, b] : EuclideanSpace ℝ (Fin 2))
      (!₂[c, d] : EuclideanSpace ℝ (Fin 2)) =
        (Real.arctan (d / c) - Real.arctan (b / a) : ℝ) := by
    rw [← orientation.oangle_sub_left he hleftNe hrightNe,
      hfirst, hsecond, Real.Angle.coe_sub]
  rw [hangle]
  apply Real.Angle.toReal_coe_eq_self_iff.mpr
  have hdRange := Real.arctan_mem_Ioo (d / c)
  have hbRange := Real.arctan_mem_Ioo (b / a)
  constructor
  · linarith [hdRange.1, hdRange.2, hbRange.1, hbRange.2]
  · linarith [hdRange.1, hdRange.2, hbRange.1, hbRange.2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The principal real oriented angle is smooth wherever both vectors remain in the positive
first-coordinate chart. -/
theorem contDiffAt_oangle_toReal_of_pos (k : ℕ∞ω) {a b c d : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ k a x) (hb : ContDiffAt ℝ k b x)
    (hc : ContDiffAt ℝ k c x) (hd : ContDiffAt ℝ k d x)
    (hax : 0 < a x) (hcx : 0 < c x) :
    ContDiffAt ℝ k (fun y ↦
      (orientation.oangle
        (!₂[a y, b y] : EuclideanSpace ℝ (Fin 2))
        (!₂[c y, d y] : EuclideanSpace ℝ (Fin 2))).toReal) x := by
  have haPos : ∀ᶠ y in 𝓝 x, 0 < a y :=
    ha.continuousAt.eventually (Ioi_mem_nhds hax)
  have hcPos : ∀ᶠ y in 𝓝 x, 0 < c y :=
    hc.continuousAt.eventually (Ioi_mem_nhds hcx)
  have hsmooth : ContDiffAt ℝ k
      (fun y ↦ Real.arctan (d y / c y) - Real.arctan (b y / a y)) x := by
    have hright := Real.contDiff_arctan.contDiffAt.comp x (hd.div hc hcx.ne')
    have hleft := Real.contDiff_arctan.contDiffAt.comp x (hb.div ha hax.ne')
    exact hright.sub hleft
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [haPos, hcPos] with y hay hcy
  exact oangle_toReal_eq_arctan_sub_of_pos (a y) (b y) (c y) (d y) hay hcy

end EuclideanPlane
