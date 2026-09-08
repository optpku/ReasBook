module

public import ReasLib.Geometry.Euclidean.Plane.Rotation
public import ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.Geometry.Euclidean.Plane.Rotation
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

public section

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace EuclideanPlane.SignedAngle

/-- The ambient half-plane chart around the identity rotation matrix. -/
def chart : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {M | 0 < M 0 0}

/-- The local signed-angle coordinate obtained from the lower-left and upper-left entries. -/
def coordinate (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.arctan (M 1 0 / M 0 0)

/-- Membership in the signed-angle chart is positivity of the upper-left entry. -/
theorem mem_chart (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M ∈ chart ↔ 0 < M 0 0 := by
  -- Unfolding the chart reduces membership to its defining positivity condition.
  rfl

/-- The signed-angle chart is open in the ambient matrix space. -/
theorem isOpen_chart : IsOpen chart := by
  -- The chart is the inverse image of the positive half-line under entry evaluation.
  have hentry : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 0) :=
    (continuous_apply 0).comp (continuous_apply 0)
  simpa [chart] using isOpen_lt continuous_const hentry

/-- The identity matrix belongs to the signed-angle chart. -/
theorem one_mem_chart : (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ chart := by
  -- The upper-left entry of the identity matrix is one.
  simp [chart]

/-- The signed-angle coordinate of the identity matrix is zero. -/
theorem coordinate_one : coordinate (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  -- Both off-diagonal entries vanish at the identity.
  simp [coordinate]

/-- Every signed-angle coordinate lies in the arctangent branch interval. -/
theorem coordinate_mem_interval (M : Matrix (Fin 2) (Fin 2) ℝ) :
    coordinate M ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  -- This is the canonical range of the real arctangent.
  exact Real.arctan_mem_Ioo (M 1 0 / M 0 0)

/-- The real arctangent is analytic at every real point. -/
private lemma analyticAt_arctan (x : ℝ) : AnalyticAt ℝ Real.arctan x := by
  let y := Real.arctan x
  have hy : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := Real.arctan_mem_Ioo x
  have hcos : Real.cos y ≠ 0 := (Real.cos_pos_of_mem_Ioo hy).ne'
  have htan : AnalyticAt ℝ Real.tan y := by
    apply AnalyticAt.congr (Real.analyticAt_sin.div Real.analyticAt_cos hcos)
    filter_upwards with z
    exact (Real.tan_eq_sin_div_cos z).symm
  have hderiv : deriv Real.tan y ≠ 0 := by
    rw [Real.deriv_tan]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 hcos)
  have hinverse : AnalyticAt ℝ (Real.arctan ∘ Real.tan) y := by
    apply analyticAt_id.congr
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    simpa only [id_eq, Function.comp_apply] using (Real.arctan_tan hz.1 hz.2).symm
  -- Analyticity passes from the local identity through the locally invertible tangent.
  simpa [y, Real.tan_arctan] using
    (analyticAt_comp_iff_of_deriv_ne_zero htan hderiv).mp hinverse

/-- The signed-angle coordinate is real-analytic throughout the identity chart. -/
theorem analyticOnNhd_coordinate : AnalyticOnNhd ℝ coordinate chart := by
  intro M hM
  have hrowOne : AnalyticAt ℝ (fun N : Matrix (Fin 2) (Fin 2) ℝ ↦ N 1) M := by
    exact analyticAt_pi_iff.mp analyticAt_id 1
  have hnum : AnalyticAt ℝ (fun N : Matrix (Fin 2) (Fin 2) ℝ ↦ N 1 0) M := by
    exact analyticAt_pi_iff.mp hrowOne 0
  have hrowZero : AnalyticAt ℝ (fun N : Matrix (Fin 2) (Fin 2) ℝ ↦ N 0) M := by
    exact analyticAt_pi_iff.mp analyticAt_id 0
  have hden : AnalyticAt ℝ (fun N : Matrix (Fin 2) (Fin 2) ℝ ↦ N 0 0) M := by
    exact analyticAt_pi_iff.mp hrowZero 0
  have hpos : 0 < M 0 0 := (mem_chart M).mp hM
  have hquot : AnalyticAt ℝ (fun N : Matrix (Fin 2) (Fin 2) ℝ ↦ N 1 0 / N 0 0) M :=
    hnum.div hden hpos.ne'
  -- Compose the analytic quotient of entries with the analytic arctangent.
  have hcomp := AnalyticAt.comp
    (f := fun N : Matrix (Fin 2) (Fin 2) ℝ ↦ N 1 0 / N 0 0)
    (analyticAt_arctan (M 1 0 / M 0 0)) hquot
  apply hcomp.congr
  filter_upwards with N
  rfl

/-- On the local branch interval, the coordinate recovers the real rotation parameter. -/
theorem coordinate_rotationMatrix (phi : ℝ)
    (hphi : phi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    coordinate (EuclideanPlane.rotationMatrix phi) = phi := by
  -- The two entries form the tangent of `phi` on the chosen branch.
  simpa [coordinate, EuclideanPlane.rotationMatrix, Real.tan_eq_sin_div_cos] using
    Real.arctan_tan hphi.1 hphi.2

/-- A special orthogonal matrix in the identity chart is recovered from its coordinate. -/
theorem rotationMatrix_coordinate (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (hchart : M ∈ chart) :
    EuclideanPlane.rotationMatrix (coordinate M) = M := by
  have hpos : 0 < M 0 0 := (mem_chart M).mp hchart
  obtain ⟨hdiag, hoffdiag, hunit⟩ :=
    (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp hM)
  have hunit' : M 0 0 ^ 2 + M 1 0 ^ 2 = 1 := by
    rw [hoffdiag] at hunit
    nlinarith
  have hradicand : 0 ≤ 1 + (M 1 0 / M 0 0) ^ 2 := by
    positivity
  have hinverse : 0 ≤ 1 / M 0 0 := by
    positivity
  have hsqrt : Real.sqrt (1 + (M 1 0 / M 0 0) ^ 2) = 1 / M 0 0 := by
    apply (Real.sqrt_eq_iff_mul_self_eq hradicand hinverse).2
    field_simp
    nlinarith
  have hcos : Real.cos (Real.arctan (M 1 0 / M 0 0)) = M 0 0 := by
    rw [Real.cos_arctan, hsqrt]
    field_simp
  have hsin : Real.sin (Real.arctan (M 1 0 / M 0 0)) = M 1 0 := by
    rw [Real.sin_arctan, hsqrt]
    field_simp
  -- The SO(2) relations identify all four entries with the reconstructed rotation.
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [coordinate, EuclideanPlane.rotationMatrix] using hcos
    · simpa [coordinate, EuclideanPlane.rotationMatrix, hoffdiag] using congrArg Neg.neg hsin
  · fin_cases j
    · simpa [coordinate, EuclideanPlane.rotationMatrix] using hsin
    · simpa [coordinate, EuclideanPlane.rotationMatrix, hdiag] using hcos

/-- The local real parameter of a special orthogonal matrix is uniquely its coordinate. -/
theorem coordinate_unique (M : Matrix (Fin 2) (Fin 2) ℝ) (phi : ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (hchart : M ∈ chart)
    (hphi : phi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    EuclideanPlane.rotationMatrix phi = M ↔ phi = coordinate M := by
  constructor
  · intro hmatrix
    have hcoordinate := congrArg coordinate hmatrix
    simpa only [coordinate_rotationMatrix phi hphi] using hcoordinate
  · intro hphiCoordinate
    rw [hphiCoordinate]
    exact rotationMatrix_coordinate M hM hchart

/-- On the local branch, the matrix coordinate agrees with the canonical real angle
representative. -/
theorem coordinate_rotationMatrix_toReal (theta : Real.Angle)
    (htheta : theta.toReal ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    coordinate (EuclideanPlane.rotationMatrix theta) = theta.toReal := by
  have hmatrix : EuclideanPlane.rotationMatrix theta.toReal =
      EuclideanPlane.rotationMatrix theta := by
    rw [Real.Angle.coe_toReal]
  rw [← hmatrix]
  exact coordinate_rotationMatrix theta.toReal htheta

end EuclideanPlane.SignedAngle
