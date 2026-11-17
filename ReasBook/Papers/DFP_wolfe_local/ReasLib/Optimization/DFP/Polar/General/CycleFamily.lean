module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2
public import ReasLib.Optimization.DFP.Polar.Normalized.Dynamics
public import ReasLib.Optimization.DFP.Polar.FastContraction
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Topology.Order.Basic

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.Polar.General

/-- The even coefficient in the general rational family `eq:polar-family`. -/
def cycleLambdaEven (δE δO ν : ℝ) : ℝ :=
  ν * (δO + ν) / (δO - δE + 2 * ν)

/-- The odd coefficient in the general rational family `eq:polar-family`. -/
def cycleLambdaOdd (δE δO ν : ℝ) : ℝ :=
  ν * (δE - ν) / (δO - δE + 2 * ν)

/-- The preserved diagonal coordinate in the family `eq:polar-family`. -/
def cycleGamma (δE δO ν : ℝ) : ℝ :=
  (δO - δE + 2 * ν) / (ν * (δE - ν) * (δO + ν))

/-- The nonvanishing positive factors of `eq:polar-family`. -/
structure CycleDomain (δE δO ν : ℝ) : Prop where
  nu_pos : 0 < ν
  even_gap_pos : 0 < δE - ν
  odd_gap_pos : 0 < δO + ν
  denominator_pos : 0 < δO - δE + 2 * ν

/-- The manuscript's positivity interval lies in the domain of `eq:polar-family`. -/
theorem cycleDomainOfInterval {δE δO ν : ℝ} (hδO : 0 < δO)
    (hlo : max 0 ((δE - δO) / 2) < ν) (hhi : ν < δE) :
    CycleDomain δE δO ν := by
  have hν : 0 < ν := lt_of_le_of_lt (le_max_left _ _) hlo
  have hden : (δE - δO) / 2 < ν := lt_of_le_of_lt (le_max_right _ _) hlo
  constructor
  · exact hν
  · exact sub_pos.mpr hhi
  · exact add_pos hδO hν
  · linarith

/-- Every point of the positive domain of `eq:polar-family` has a domain neighborhood. -/
theorem CycleDomain.eventually {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    ∀ᶠ t in 𝓝 ν, CycleDomain δE δO t := by
  have heven : ContinuousAt (fun t : ℝ ↦ δE - t) ν :=
    continuousAt_const.sub continuousAt_id
  have hodd : ContinuousAt (fun t : ℝ ↦ δO + t) ν :=
    continuousAt_const.add continuousAt_id
  have hden : ContinuousAt (fun t : ℝ ↦ δO - δE + 2 * t) ν :=
    continuousAt_const.add (continuousAt_const.mul continuousAt_id)
  filter_upwards [eventually_gt_nhds h.nu_pos,
    heven.eventually (eventually_gt_nhds h.even_gap_pos),
    hodd.eventually (eventually_gt_nhds h.odd_gap_pos),
    hden.eventually (eventually_gt_nhds h.denominator_pos)] with t ht he ho hd
  exact ⟨ht, he, ho, hd⟩

/-- The even coefficient of `eq:polar-family` is positive on its domain. -/
theorem cycleLambdaEven_pos {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    0 < cycleLambdaEven δE δO ν := by
  exact div_pos (mul_pos h.nu_pos h.odd_gap_pos) h.denominator_pos

/-- The odd coefficient of `eq:polar-family` is positive on its domain. -/
theorem cycleLambdaOdd_pos {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    0 < cycleLambdaOdd δE δO ν := by
  exact div_pos (mul_pos h.nu_pos h.even_gap_pos) h.denominator_pos

/-- The diagonal coefficient of `eq:polar-family` is positive on its domain. -/
theorem cycleGamma_pos {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    0 < cycleGamma δE δO ν := by
  exact div_pos h.denominator_pos
    (mul_pos (mul_pos h.nu_pos h.even_gap_pos) h.odd_gap_pos)

/-- The two coefficients of `eq:polar-family` differ by `ν`. -/
theorem cycleLambdaEven_sub_odd {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    cycleLambdaEven δE δO ν - cycleLambdaOdd δE δO ν = ν := by
  unfold cycleLambdaEven cycleLambdaOdd
  rw [← sub_div]
  apply (div_eq_iff h.denominator_pos.ne').mpr
  ring

/-- The reciprocal even product in `eq:polar-family` is `δE - ν`. -/
theorem one_div_cycleGamma_mul_even {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    1 / (cycleGamma δE δO ν * cycleLambdaEven δE δO ν) = δE - ν := by
  unfold cycleGamma cycleLambdaEven
  field_simp [h.nu_pos.ne', h.even_gap_pos.ne', h.odd_gap_pos.ne',
    h.denominator_pos.ne']

/-- The reciprocal odd product in `eq:polar-family` is `δO + ν`. -/
theorem one_div_cycleGamma_mul_odd {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    1 / (cycleGamma δE δO ν * cycleLambdaOdd δE δO ν) = δO + ν := by
  unfold cycleGamma cycleLambdaOdd
  field_simp [h.nu_pos.ne', h.even_gap_pos.ne', h.odd_gap_pos.ne',
    h.denominator_pos.ne']

/-- The first stage maps the even coefficient to the odd coefficient. -/
theorem cycleMatchingEven {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    cycleLambdaEven δE δO ν +
        1 / (cycleGamma δE δO ν * cycleLambdaEven δE δO ν) - δE =
      cycleLambdaOdd δE δO ν := by
  rw [one_div_cycleGamma_mul_even h]
  linarith [cycleLambdaEven_sub_odd h]

/-- The second stage maps the odd coefficient to the even coefficient. -/
theorem cycleMatchingOdd {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    cycleLambdaOdd δE δO ν +
        1 / (cycleGamma δE δO ν * cycleLambdaOdd δE δO ν) - δO =
      cycleLambdaEven δE δO ν := by
  rw [one_div_cycleGamma_mul_odd h]
  linarith [cycleLambdaEven_sub_odd h]

/-- The symmetric state matrix used in `eq:polar-two-cycle`. -/
def cycleMatrix (γ lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  RealSymmetric2.matrix γ (γ * lam) (1 + γ * lam ^ 2)

/-- The determinant of each state matrix in `eq:polar-two-cycle` is `γ`. -/
theorem cycleMatrix_det (γ lam : ℝ) : (cycleMatrix γ lam).det = γ := by
  simp only [cycleMatrix, RealSymmetric2.matrix_eq, Matrix.det_fin_two]
  simp
  ring

/-- The quadratic form of `eq:polar-two-cycle` is a sum of two squares. -/
theorem cycleMatrix_quadratic (γ lam : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (cycleMatrix γ lam *ᵥ x) =
      γ * (x 0 + lam * x 1) ^ 2 + (x 1) ^ 2 := by
  simp [cycleMatrix, RealSymmetric2.matrix_eq, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two]
  ring

/-- A positive preserved diagonal makes the state matrix positive definite. -/
theorem cycleMatrix_posDef {γ : ℝ} (hγ : 0 < γ) (lam : ℝ) :
    (cycleMatrix γ lam).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨RealSymmetric2.matrix_isHermitian _ _ _, ?_⟩
  intro x hx
  rw [cycleMatrix_quadratic]
  by_cases hx1 : x 1 = 0
  · have hx0 : x 0 ≠ 0 := by
      intro hz
      apply hx
      ext i
      fin_cases i
      · exact hz
      · exact hx1
    simpa [hx1] using mul_pos hγ (sq_pos_of_ne_zero hx0)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg hγ.le (sq_nonneg _)) (sq_pos_of_ne_zero hx1)

/-- The three normalized coordinates of the state matrix in `eq:polar-two-cycle`. -/
def cycleState (γ lam : ℝ) : ℝ × ℝ × ℝ :=
  (γ, γ * lam, 1 + γ * lam ^ 2)

/-- The coordinate formula for a normalized quadratic state. -/
theorem cycleState_apply (γ lam : ℝ) :
    cycleState γ lam = (γ, γ * lam, 1 + γ * lam ^ 2) := by
  rfl

/-- The even state on the rational family `eq:polar-family`. -/
def evenState (δE δO ν : ℝ) : ℝ × ℝ × ℝ :=
  cycleState (cycleGamma δE δO ν) (cycleLambdaEven δE δO ν)

/-- The odd state on the rational family `eq:polar-family`. -/
def oddState (δE δO ν : ℝ) : ℝ × ℝ × ℝ :=
  cycleState (cycleGamma δE δO ν) (cycleLambdaOdd δE δO ν)

/-- The slope of a normalized quadratic state is its coefficient plus a reciprocal. -/
theorem slope_cycleState {γ lam : ℝ} (hγ : γ ≠ 0) (hlam : lam ≠ 0) :
    Normalized.slope (cycleState γ lam) = lam + 1 / (γ * lam) := by
  rw [Normalized.slope_def, cycleState_apply]
  dsimp only
  field_simp [hγ, hlam]
  ring

/-- The even slope is the next coefficient plus the even angular increment. -/
theorem slope_evenState {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    Normalized.slope (evenState δE δO ν) = cycleLambdaOdd δE δO ν + δE := by
  unfold evenState
  rw [slope_cycleState (cycleGamma_pos h).ne' (cycleLambdaEven_pos h).ne']
  linarith [cycleMatchingEven h]

/-- The odd slope is the next coefficient plus the odd angular increment. -/
theorem slope_oddState {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    Normalized.slope (oddState δE δO ν) = cycleLambdaEven δE δO ν + δO := by
  unfold oddState
  rw [slope_cycleState (cycleGamma_pos h).ne' (cycleLambdaOdd_pos h).ne']
  linarith [cycleMatchingOdd h]

/-- The even limiting stage maps the even rational state to the odd state. -/
theorem evenToOdd {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    Normalized.leadingStage δE (evenState δE δO ν) = oddState δE δO ν := by
  rw [Normalized.leadingStage_apply, ← Normalized.slope_def, slope_evenState h]
  simp [evenState, oddState, cycleState_apply]

/-- The odd limiting stage returns the odd rational state to the even state. -/
theorem oddToEven {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    Normalized.leadingStage δO (oddState δE δO ν) = evenState δE δO ν := by
  rw [Normalized.leadingStage_apply, ← Normalized.slope_def, slope_oddState h]
  simp [evenState, oddState, cycleState_apply]

/-- A complete limiting cycle fixes the even rational state. -/
theorem twoCycle_evenState {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    Normalized.leadingStage δO (Normalized.leadingStage δE (evenState δE δO ν)) =
      evenState δE δO ν := by
  rw [evenToOdd h, oddToEven h]

/-- The even rational state reconstructs a positive definite matrix. -/
theorem evenState_posDef {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    (RealSymmetric2.matrix (evenState δE δO ν).1
      (evenState δE δO ν).2.1 (evenState δE δO ν).2.2).PosDef := by
  exact cycleMatrix_posDef (cycleGamma_pos h) _

/-- The odd rational state reconstructs a positive definite matrix. -/
theorem oddState_posDef {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    (RealSymmetric2.matrix (oddState δE δO ν).1
      (oddState δE δO ν).2.1 (oddState δE δO ν).2.2).PosDef := by
  exact cycleMatrix_posDef (cycleGamma_pos h) _

/-- The determinant of the even rational state is the preserved diagonal. -/
theorem evenState_det (δE δO ν : ℝ) :
    (RealSymmetric2.matrix (evenState δE δO ν).1
      (evenState δE δO ν).2.1 (evenState δE δO ν).2.2).det = cycleGamma δE δO ν := by
  exact cycleMatrix_det _ _

/-- The determinant of the odd rational state is the preserved diagonal. -/
theorem oddState_det (δE δO ν : ℝ) :
    (RealSymmetric2.matrix (oddState δE δO ν).1
      (oddState δE δO ν).2.1 (oddState δE δO ν).2.2).det = cycleGamma δE δO ν := by
  exact cycleMatrix_det _ _

/-- The even angular coefficient selected from the auxiliary base parameters. -/
def baseDeltaEven (ell z : ℝ) : ℝ := ell - 1 + z

/-- The odd angular coefficient selected from the auxiliary base parameters. -/
def baseDeltaOdd (ell z : ℝ) : ℝ := 1 - ell + z * ell

/-- The positive rational-family parameter at a nondegenerate base point. -/
def baseNu (ell : ℝ) : ℝ := ell - 1

/-- The normalization at the chosen base point. -/
def baseGamma (ell z : ℝ) : ℝ := 1 / (z * ell)

/-- The transverse eigenvalue at the chosen base point. -/
def baseKappa (ell z : ℝ) : ℝ := (1 - z / ell) * (1 - z * ell)

/-- The even limiting curvature ratio at the chosen base point. -/
def curvatureEven (ell z : ℝ) : ℝ := 1 / (ell + z)

/-- The odd limiting curvature ratio at the chosen base point. -/
def curvatureOdd (ell z : ℝ) : ℝ := ell / (1 + z * ell)

/-- Strict Wolfe inequalities and transverse stability for one base point. -/
structure StrictWolfeBase (c1 c2 ell z : ℝ) : Prop where
  one_lt_ell : 1 < ell
  z_pos : 0 < z
  deltaOdd_pos : 0 < baseDeltaOdd ell z
  stable : |baseKappa ell z| < 1
  even_curvature_lt : curvatureEven ell z < c2
  odd_curvature_lt : curvatureOdd ell z < c2
  even_armijo_lt : c1 < (1 + curvatureEven ell z) / 2
  odd_armijo_lt : c1 < (1 + curvatureOdd ell z) / 2

/-- The even angular coefficient at a strict Wolfe base is positive. -/
theorem StrictWolfeBase.deltaEven_pos {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) : 0 < baseDeltaEven ell z := by
  dsimp [baseDeltaEven]
  linarith [h.one_lt_ell, h.z_pos]

/-- The two base gaps and the family denominator have factored forms. -/
theorem baseFamilyFactors (ell z : ℝ) :
    baseDeltaEven ell z - baseNu ell = z ∧
      baseDeltaOdd ell z + baseNu ell = z * ell ∧
      baseDeltaOdd ell z - baseDeltaEven ell z + 2 * baseNu ell =
        z * (ell - 1) := by
  dsimp [baseDeltaEven, baseDeltaOdd, baseNu]
  constructor
  · ring
  · constructor
    · ring
    · ring

/-- Nondegenerate positive auxiliary parameters define a valid family point. -/
theorem baseCycleDomain {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    CycleDomain (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseNu ell) := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  constructor
  · exact sub_pos.mpr hell
  · rw [(baseFamilyFactors ell z).1]
    exact hz
  · rw [(baseFamilyFactors ell z).2.1]
    exact mul_pos hz hellpos
  · rw [(baseFamilyFactors ell z).2.2]
    exact mul_pos hz (sub_pos.mpr hell)

/-- The even rational coefficient at the base point is `ell`. -/
theorem cycleLambdaEven_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    cycleLambdaEven (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseNu ell) =
      ell := by
  unfold cycleLambdaEven
  rw [(baseFamilyFactors ell z).2.1, (baseFamilyFactors ell z).2.2]
  dsimp [baseNu]
  apply (div_eq_iff (mul_pos hz (sub_pos.mpr hell)).ne').mpr
  ring

/-- The odd rational coefficient at the base point is one. -/
theorem cycleLambdaOdd_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    cycleLambdaOdd (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseNu ell) =
      1 := by
  unfold cycleLambdaOdd
  rw [(baseFamilyFactors ell z).1, (baseFamilyFactors ell z).2.2]
  dsimp [baseNu]
  apply (div_eq_iff (mul_pos hz (sub_pos.mpr hell)).ne').mpr
  ring

/-- The rational diagonal coefficient specializes to the base normalization. -/
theorem cycleGamma_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    cycleGamma (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseNu ell) =
      baseGamma ell z := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  unfold cycleGamma
  rw [(baseFamilyFactors ell z).1, (baseFamilyFactors ell z).2.1,
    (baseFamilyFactors ell z).2.2]
  dsimp [baseNu, baseGamma]
  field_simp [hz.ne', hellpos.ne', (sub_pos.mpr hell).ne']

/-- The even family state at the chosen parameter has coefficient `ell`. -/
theorem evenState_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    evenState (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseNu ell) =
      cycleState (baseGamma ell z) ell := by
  unfold evenState
  rw [cycleGamma_base hell hz, cycleLambdaEven_base hell hz]

/-- The odd family state at the chosen parameter has coefficient one. -/
theorem oddState_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    oddState (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseNu ell) =
      cycleState (baseGamma ell z) 1 := by
  unfold oddState
  rw [cycleGamma_base hell hz, cycleLambdaOdd_base hell hz]

/-- At the reference value `ell = 1`, both curvature ratios coincide. -/
theorem curvature_reference (z : ℝ) :
    curvatureEven 1 z = 1 / (1 + z) ∧ curvatureOdd 1 z = 1 / (1 + z) := by
  simp [curvatureEven, curvatureOdd]

/-- At the reference value `ell = 1`, the transverse eigenvalue is a square. -/
theorem baseKappa_reference (z : ℝ) : baseKappa 1 z = (1 - z) ^ 2 := by
  simp [baseKappa, pow_two]

/-- The nilpotent choice `z = ell` has zero transverse eigenvalue. -/
theorem baseKappa_diagonal {ell : ℝ} (hell : ell ≠ 0) :
    baseKappa ell ell = 0 := by
  simp [baseKappa, hell]

/-- Curvature and stability vary continuously near the reference base point. -/
private theorem baseFunctionsContinuous {z : ℝ} (hz : 0 < z) :
    ContinuousAt (fun ell : ℝ ↦ baseDeltaOdd ell z) 1 ∧
      ContinuousAt (fun ell : ℝ ↦ |baseKappa ell z|) 1 ∧
      ContinuousAt (fun ell : ℝ ↦ curvatureEven ell z) 1 ∧
      ContinuousAt (fun ell : ℝ ↦ curvatureOdd ell z) 1 := by
  have hsum : 1 + z ≠ 0 := ne_of_gt (add_pos zero_lt_one hz)
  have hden : 1 + z * 1 ≠ 0 := by simpa using hsum
  have hcE : ContinuousAt (fun ell : ℝ ↦ curvatureEven ell z) 1 :=
    continuousAt_const.div (continuousAt_id.add continuousAt_const) hsum
  have hcO : ContinuousAt (fun ell : ℝ ↦ curvatureOdd ell z) 1 :=
    continuousAt_id.div (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) hden
  refine ⟨?_, ?_, hcE, hcO⟩
  · exact (continuousAt_const.sub continuousAt_id).add
      (continuousAt_const.mul continuousAt_id)
  · apply ContinuousAt.abs
    exact (continuousAt_const.sub (continuousAt_const.div continuousAt_id one_ne_zero)).mul
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))

/-- Strict reference inequalities persist at some genuine base point `ell > 1`. -/
private theorem strictWolfeBaseOfReference {c1 c2 z : ℝ} (hz : 0 < z)
    (hz2 : z < 2) (hc : 1 / (1 + z) < c2)
    (ha : c1 < (1 + 1 / (1 + z)) / 2) :
    ∃ ell : ℝ, StrictWolfeBase c1 c2 ell z := by
  have hcont := baseFunctionsContinuous hz
  have hstable : |baseKappa 1 z| < 1 := by
    rw [baseKappa_reference, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hdelta : 0 < baseDeltaOdd 1 z := by simpa [baseDeltaOdd] using hz
  have hcE : curvatureEven 1 z < c2 := by
    simpa [curvatureEven] using hc
  have hcO : curvatureOdd 1 z < c2 := by
    simpa [curvatureOdd] using hc
  have haE : c1 < (1 + curvatureEven 1 z) / 2 := by
    simpa [curvatureEven] using ha
  have haO : c1 < (1 + curvatureOdd 1 z) / 2 := by
    simpa [curvatureOdd] using ha
  have hcontAE : ContinuousAt (fun ell : ℝ ↦ (1 + curvatureEven ell z) / 2) 1 :=
    (continuousAt_const.add hcont.2.2.1).div_const 2
  have hcontAO : ContinuousAt (fun ell : ℝ ↦ (1 + curvatureOdd ell z) / 2) 1 :=
    (continuousAt_const.add hcont.2.2.2).div_const 2
  have hevent : ∀ᶠ ell : ℝ in 𝓝 1,
      0 < baseDeltaOdd ell z ∧ |baseKappa ell z| < 1 ∧
        curvatureEven ell z < c2 ∧ curvatureOdd ell z < c2 ∧
        c1 < (1 + curvatureEven ell z) / 2 ∧
        c1 < (1 + curvatureOdd ell z) / 2 := by
    filter_upwards [hcont.1.eventually (eventually_gt_nhds hdelta),
      hcont.2.1.eventually (eventually_lt_nhds hstable),
      hcont.2.2.1.eventually (eventually_lt_nhds hcE),
      hcont.2.2.2.eventually (eventually_lt_nhds hcO),
      hcontAE.eventually (eventually_gt_nhds haE),
      hcontAO.eventually (eventually_gt_nhds haO)] with ell hd hs he ho hae hao
    exact ⟨hd, hs, he, ho, hae, hao⟩
  obtain ⟨a, b, hab, hsub⟩ := hevent.exists_Ioo_subset
  obtain ⟨ell, hell, helb⟩ := exists_between hab.2
  have hmem : ell ∈ Set.Ioo a b := ⟨lt_trans hab.1 hell, helb⟩
  have h := hsub hmem
  exact ⟨ell, ⟨hell, hz, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

/-- If `c2 > 1/3`, a perturbation of `ell = 1` gives a strict stable base. -/
private theorem strictWolfeBaseAboveThird {c1 c2 : ℝ}
    (hc12 : c1 < c2) (hc2 : c2 < 1) (hthird : (1 : ℝ) / 3 < c2) :
    ∃ ell z : ℝ, StrictWolfeBase c1 c2 ell z := by
  have hlower : max ((1 : ℝ) / 3) (2 * c1 - 1) < c2 := by
    apply max_lt hthird
    linarith
  obtain ⟨w, hwlo, hwc2⟩ := exists_between hlower
  have hwthird : (1 : ℝ) / 3 < w := lt_of_le_of_lt (le_max_left _ _) hwlo
  have hwarmijo : 2 * c1 - 1 < w := lt_of_le_of_lt (le_max_right _ _) hwlo
  have hw : 0 < w := by linarith
  have hw1 : w < 1 := lt_trans hwc2 hc2
  let z := 1 / w - 1
  have hz : 0 < z := by
    dsimp [z]
    have hmul : 1 * w < 1 := by simpa using hw1
    exact sub_pos.mpr ((lt_div_iff₀ hw).mpr hmul)
  have hz2 : z < 2 := by
    dsimp [z]
    have hmul : 1 < 3 * w := by linarith
    have hquot : 1 / w < 3 := (div_lt_iff₀ hw).mpr hmul
    linarith
  have hinv : 1 / (1 + z) = w := by
    dsimp [z]
    field_simp
    ring
  have hcurvature : 1 / (1 + z) < c2 := by rwa [hinv]
  have harmijo : c1 < (1 + 1 / (1 + z)) / 2 := by
    rw [hinv]
    linarith
  obtain ⟨ell, hbase⟩ := strictWolfeBaseOfReference hz hz2 hcurvature harmijo
  exact ⟨ell, z, hbase⟩

/-- If `c2 ≤ 1/3`, the choice `z = ell` gives strict Wolfe margins and stability. -/
private theorem strictWolfeBaseBelowThird {c1 c2 : ℝ}
    (hc2 : 0 < c2) (hc12 : c1 < c2) (hthird : c2 ≤ (1 : ℝ) / 3) :
    ∃ ell z : ℝ, StrictWolfeBase c1 c2 ell z := by
  obtain ⟨ell, hellmax⟩ := exists_gt (max (3 : ℝ) (1 / c2))
  have hell3 : 3 < ell := lt_of_le_of_lt (le_max_left _ _) hellmax
  have hellinv : 1 / c2 < ell := lt_of_le_of_lt (le_max_right _ _) hellmax
  have hell : 1 < ell := by linarith
  have hellpos : 0 < ell := by linarith
  have hden : 0 < 1 + ell * ell := by positivity
  have hrecip : 1 / ell < c2 := by
    apply (div_lt_iff₀ hellpos).mpr
    have h := (div_lt_iff₀ hc2).mp hellinv
    nlinarith
  have hepos : 0 < curvatureEven ell ell := by
    exact one_div_pos.mpr (add_pos hellpos hellpos)
  have hopos : 0 < curvatureOdd ell ell := div_pos hellpos hden
  have he : curvatureEven ell ell < c2 := by
    apply lt_trans _ hrecip
    have hdouble : ell < ell + ell := by linarith
    exact one_div_lt_one_div_of_lt hellpos hdouble
  have ho : curvatureOdd ell ell < c2 := by
    apply lt_trans _ hrecip
    apply (div_lt_div_iff₀ hden hellpos).mpr
    nlinarith
  refine ⟨ell, ell, hell, hellpos, ?_, ?_, he, ho, ?_, ?_⟩
  · dsimp [baseDeltaOdd]
    nlinarith [sq_nonneg (ell - 1)]
  · rw [baseKappa_diagonal hellpos.ne']
    norm_num
  · linarith
  · linarith

/-- Every Wolfe pair `0 < c1 < c2 < 1` admits a strict stable general two-cycle. -/
theorem strictWolfeBaseExists {c1 c2 : ℝ} (hc1 : 0 < c1)
    (hc12 : c1 < c2) (hc2 : c2 < 1) :
    ∃ ell z : ℝ, StrictWolfeBase c1 c2 ell z := by
  by_cases hthird : (1 : ℝ) / 3 < c2
  · exact strictWolfeBaseAboveThird hc12 hc2 hthird
  · exact strictWolfeBaseBelowThird (lt_trans hc1 hc12) hc12 (le_of_not_gt hthird)

/-- The quotient derivative of the general normalization in `eq:polar-family`. -/
def cycleGammaDerivative (δE δO ν : ℝ) : ℝ :=
  (2 * (ν * (δE - ν) * (δO + ν)) -
      (δO - δE + 2 * ν) *
        ((δE - 2 * ν) * (δO + ν) + ν * (δE - ν))) /
    (ν * (δE - ν) * (δO + ν)) ^ 2

/-- The general normalization has its rational strict derivative throughout its domain. -/
theorem hasStrictDerivAt_cycleGamma {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    HasStrictDerivAt (cycleGamma δE δO) (cycleGammaDerivative δE δO ν) ν := by
  have hid : HasStrictDerivAt (fun t : ℝ ↦ t) 1 ν := hasStrictDerivAt_id ν
  have hnum : HasStrictDerivAt (fun t : ℝ ↦ δO - δE + 2 * t) (2 * 1) ν :=
    (hid.const_mul 2).const_add (δO - δE)
  have hden := (hid.mul (hid.const_sub δE)).mul (hid.const_add δO)
  have hd := hnum.fun_div hden
    (mul_ne_zero (mul_ne_zero h.nu_pos.ne' h.even_gap_pos.ne') h.odd_gap_pos.ne')
  have hvalue :
      ((2 * 1) * (ν * (δE - ν) * (δO + ν)) -
          (δO - δE + 2 * ν) *
            ((1 * (δE - ν) + ν * -1) * (δO + ν) +
              ν * (δE - ν) * 1)) /
        (ν * (δE - ν) * (δO + ν)) ^ 2 = cycleGammaDerivative δE δO ν := by
    unfold cycleGammaDerivative
    ring
  exact hd.congr_deriv hvalue

/-- All three rational coefficients in `eq:polar-family` are analytic on the domain. -/
theorem cycleFamily_analyticAt {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    AnalyticAt ℝ (cycleLambdaEven δE δO) ν ∧
      AnalyticAt ℝ (cycleLambdaOdd δE δO) ν ∧
      AnalyticAt ℝ (cycleGamma δE δO) ν := by
  have hid : AnalyticAt ℝ (fun t : ℝ ↦ t) ν := analyticAt_id
  have heven : AnalyticAt ℝ (fun t : ℝ ↦ δE - t) ν := analyticAt_const.sub hid
  have hodd : AnalyticAt ℝ (fun t : ℝ ↦ δO + t) ν := analyticAt_const.add hid
  have hnum : AnalyticAt ℝ (fun t : ℝ ↦ δO - δE + 2 * t) ν :=
    analyticAt_const.add (analyticAt_const.mul hid)
  have hden := (hid.mul heven).mul hodd
  exact ⟨(hid.mul hodd).div hnum h.denominator_pos.ne',
    (hid.mul heven).div hnum h.denominator_pos.ne',
    hnum.div hden (mul_ne_zero (mul_ne_zero h.nu_pos.ne' h.even_gap_pos.ne')
      h.odd_gap_pos.ne')⟩

/-- The normalization derivative at a base point is determined by its transverse eigenvalue. -/
def baseGammaDerivative (ell z : ℝ) : ℝ :=
  (1 - baseKappa ell z) / (z ^ 3 * ell * (ell - 1))

/-- Substitution at the base point gives the derivative formula from the manuscript. -/
theorem cycleGammaDerivative_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    cycleGammaDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseNu ell) =
      baseGammaDerivative ell z := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  unfold cycleGammaDerivative
  rw [(baseFamilyFactors ell z).1, (baseFamilyFactors ell z).2.1,
    (baseFamilyFactors ell z).2.2]
  dsimp [baseDeltaEven, baseNu, baseGammaDerivative, baseKappa]
  field_simp [hz.ne', hellpos.ne', (sub_pos.mpr hell).ne']
  ring

/-- The strict derivative of the normalization at any nondegenerate base point. -/
theorem hasStrictDerivAt_cycleGamma_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    HasStrictDerivAt (cycleGamma (baseDeltaEven ell z) (baseDeltaOdd ell z))
      (baseGammaDerivative ell z) (baseNu ell) := by
  rw [← cycleGammaDerivative_base hell hz]
  exact hasStrictDerivAt_cycleGamma (baseCycleDomain hell hz)

/-- Transverse stability makes the normalization derivative at the base positive. -/
theorem StrictWolfeBase.gammaDerivative_pos {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) : 0 < baseGammaDerivative ell z := by
  have hellpos : 0 < ell := lt_trans zero_lt_one h.one_lt_ell
  have hκ : baseKappa ell z < 1 := lt_of_le_of_lt (le_abs_self _) h.stable
  exact div_pos (sub_pos.mpr hκ)
    (mul_pos (mul_pos (pow_pos h.z_pos 3) hellpos) (sub_pos.mpr h.one_lt_ell))

/-- The normalization is analytic at every strict Wolfe base point. -/
theorem StrictWolfeBase.gamma_analyticAt {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    AnalyticAt ℝ (cycleGamma (baseDeltaEven ell z) (baseDeltaOdd ell z))
      (baseNu ell) := by
  exact (cycleFamily_analyticAt (baseCycleDomain h.one_lt_ell h.z_pos)).2.2

/-- The derivative of the normalization is nonzero at every strict Wolfe base. -/
theorem StrictWolfeBase.gamma_deriv_ne_zero {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    deriv (cycleGamma (baseDeltaEven ell z) (baseDeltaOdd ell z)) (baseNu ell) ≠ 0 := by
  rw [(hasStrictDerivAt_cycleGamma_base h.one_lt_ell h.z_pos).hasDerivAt.deriv]
  exact h.gammaDerivative_pos.ne'

/-- The analytic local inverse `ν(γ)` based at a selected strict Wolfe point. -/
def StrictWolfeBase.inverseParameter {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) : ℝ → ℝ :=
  h.gamma_analyticAt.hasStrictDerivAt.localInverse _ _ _ h.gamma_deriv_ne_zero

/-- The selected inverse is a left inverse of the rational normalization near the base parameter. -/
theorem StrictWolfeBase.inverseParameter_eventually_left {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    ∀ᶠ ν in 𝓝 (baseNu ell),
      h.inverseParameter (cycleGamma (baseDeltaEven ell z) (baseDeltaOdd ell z) ν) = ν := by
  exact h.gamma_analyticAt.hasStrictDerivAt.eventually_left_inverse h.gamma_deriv_ne_zero

/-- The selected inverse is a right inverse near the prescribed base normalization. -/
theorem StrictWolfeBase.inverseParameter_eventually_right {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    ∀ᶠ γ in 𝓝 (baseGamma ell z),
      cycleGamma (baseDeltaEven ell z) (baseDeltaOdd ell z) (h.inverseParameter γ) = γ := by
  rw [← cycleGamma_base h.one_lt_ell h.z_pos]
  exact h.gamma_analyticAt.hasStrictDerivAt.eventually_right_inverse h.gamma_deriv_ne_zero

/-- The selected inverse takes the base normalization to the base family parameter. -/
theorem StrictWolfeBase.inverseParameter_base {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    h.inverseParameter (baseGamma ell z) = baseNu ell := by
  have hi := h.inverseParameter_eventually_left.self_of_nhds
  rwa [cycleGamma_base h.one_lt_ell h.z_pos] at hi

/-- The selected local inverse is analytic at the prescribed base normalization. -/
theorem StrictWolfeBase.inverseParameter_analyticAt {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    AnalyticAt ℝ h.inverseParameter (baseGamma ell z) := by
  rw [← cycleGamma_base h.one_lt_ell h.z_pos]
  exact h.gamma_analyticAt.analyticAt_localInverse h.gamma_deriv_ne_zero

/-- The selected local inverse has derivative reciprocal to the positive
normalization derivative. -/
theorem StrictWolfeBase.hasStrictDerivAt_inverseParameter {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    HasStrictDerivAt h.inverseParameter (baseGammaDerivative ell z)⁻¹
      (baseGamma ell z) := by
  have hd := h.gamma_analyticAt.hasStrictDerivAt.to_localInverse h.gamma_deriv_ne_zero
  rw [cycleGamma_base h.one_lt_ell h.z_pos] at hd
  have hvalue :
      (deriv (cycleGamma (baseDeltaEven ell z) (baseDeltaOdd ell z)) (baseNu ell))⁻¹ =
        (baseGammaDerivative ell z)⁻¹ := by
    rw [(hasStrictDerivAt_cycleGamma_base h.one_lt_ell h.z_pos).hasDerivAt.deriv]
  exact hd.congr_deriv hvalue

/-- The selected inverse remains in the positive rational-family domain near its base value. -/
theorem StrictWolfeBase.inverseParameter_eventually_domain {c1 c2 ell z : ℝ}
    (h : StrictWolfeBase c1 c2 ell z) :
    ∀ᶠ γ in 𝓝 (baseGamma ell z),
      CycleDomain (baseDeltaEven ell z) (baseDeltaOdd ell z) (h.inverseParameter γ) := by
  have hd : ∀ᶠ ν in 𝓝 (h.inverseParameter (baseGamma ell z)),
      CycleDomain (baseDeltaEven ell z) (baseDeltaOdd ell z) ν := by
    rw [h.inverseParameter_base]
    exact (baseCycleDomain h.one_lt_ell h.z_pos).eventually
  exact h.inverseParameter_analyticAt.continuousAt.eventually hd

/-- The factored transverse Jacobian at the general two-cycle base point. -/
def baseTransverseJacobian (ell z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((1 - z * ell) / ell) • Matrix.vecMulVec ![1, 2 * ell] ![-(ell + z), 1]

/-- The four entries of the transverse base Jacobian. -/
theorem baseTransverseJacobian_apply (ell z : ℝ) :
    baseTransverseJacobian ell z =
      !![-((1 - z * ell) / ell) * (ell + z), (1 - z * ell) / ell;
        -2 * (1 - z * ell) / ell * ell * (ell + z), 2 * (1 - z * ell) / ell * ell] := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [baseTransverseJacobian]
  all_goals ring

/-- The even one-stage derivative at the general base point. -/
theorem baseStageDerivative_even {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    DFP.Polar.FastContraction.stageDerivative (baseDeltaEven ell z) (baseGamma ell z)
      (DFP.Polar.FastContraction.fastCoordinates (cycleState (baseGamma ell z) ell)) =
      ell⁻¹ • !![-(ell + z), 1; -2 * (ell + z), 2] := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  rw [DFP.Polar.FastContraction.stageDerivative_def,
    DFP.Polar.FastContraction.fastCoordinates_apply, cycleState_apply]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [baseGamma, baseDeltaEven]
  all_goals try field_simp [hz.ne', hellpos.ne']
  all_goals ring

/-- The odd one-stage derivative at the general base point. -/
theorem baseStageDerivative_odd {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    DFP.Polar.FastContraction.stageDerivative (baseDeltaOdd ell z) (baseGamma ell z)
      (DFP.Polar.FastContraction.fastCoordinates (cycleState (baseGamma ell z) 1)) =
      !![-(1 + z * ell), 1; -2 * ell * (1 + z * ell), 2 * ell] := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  rw [DFP.Polar.FastContraction.stageDerivative_def,
    DFP.Polar.FastContraction.fastCoordinates_apply, cycleState_apply]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [baseGamma, baseDeltaOdd, hz.ne', hellpos.ne']
  all_goals try field_simp [hz.ne', hellpos.ne']
  all_goals ring

/-- Multiplying the two genuine stage derivatives gives the factored base Jacobian. -/
theorem baseStageDerivative_product {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    DFP.Polar.FastContraction.stageDerivative (baseDeltaOdd ell z) (baseGamma ell z)
        (DFP.Polar.FastContraction.fastCoordinates (cycleState (baseGamma ell z) 1)) *
      DFP.Polar.FastContraction.stageDerivative (baseDeltaEven ell z) (baseGamma ell z)
        (DFP.Polar.FastContraction.fastCoordinates (cycleState (baseGamma ell z) ell)) =
      baseTransverseJacobian ell z := by
  rw [baseStageDerivative_even hell hz, baseStageDerivative_odd hell hz,
    baseTransverseJacobian_apply]
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [hellpos.ne']
  all_goals ring

/-- The trace of the base transverse Jacobian is `(1 - z / ell) * (1 - z * ell)`. -/
theorem baseTransverseJacobian_trace {ell z : ℝ} (hell : ell ≠ 0) :
    (baseTransverseJacobian ell z).trace = baseKappa ell z := by
  rw [baseTransverseJacobian_apply, Matrix.trace_fin_two]
  simp [baseKappa]
  field_simp [hell]
  ring

/-- The transverse base Jacobian has determinant zero. -/
theorem baseTransverseJacobian_det (ell z : ℝ) :
    (baseTransverseJacobian ell z).det = 0 := by
  rw [baseTransverseJacobian_apply, Matrix.det_fin_two]
  simp
  ring

/-- The base transverse Jacobian obeys the rank-one quadratic identity. -/
theorem baseTransverseJacobian_mul_self {ell z : ℝ} (hell : ell ≠ 0) :
    baseTransverseJacobian ell z * baseTransverseJacobian ell z =
      baseKappa ell z • baseTransverseJacobian ell z := by
  rw [baseTransverseJacobian_apply]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, baseKappa]
  all_goals field_simp [hell]
  all_goals ring

/-- Every positive power of the base transverse Jacobian is a scalar multiple of it. -/
theorem baseTransverseJacobian_pow {ell z : ℝ} (hell : ell ≠ 0) (n : ℕ) :
    baseTransverseJacobian ell z ^ (n + 1) =
      baseKappa ell z ^ n • baseTransverseJacobian ell z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ _ (n + 1), ih, Matrix.smul_mul, baseTransverseJacobian_mul_self hell,
      smul_smul, pow_succ]

/-- The characteristic polynomial of the base transverse Jacobian has roots zero and `baseKappa`. -/
theorem baseTransverseJacobian_charpoly {ell z : ℝ} (hell : ell ≠ 0) :
    (baseTransverseJacobian ell z).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C (baseKappa ell z)) := by
  rw [Matrix.charpoly_fin_two, baseTransverseJacobian_trace hell,
    baseTransverseJacobian_det]
  simp only [map_zero, add_zero]
  ring

/-- The stable diagonal choice has a nonzero Jacobian despite its two zero eigenvalues. -/
theorem baseTransverseJacobian_diagonal_ne_zero {ell : ℝ} (hell : 1 < ell) :
    baseTransverseJacobian ell ell ≠ 0 := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  intro hzero
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) hzero
  have hquot : (1 - ell * ell) / ell = 0 := by
    simpa [baseTransverseJacobian] using hentry
  have hnum : 1 - ell * ell = 0 := (div_eq_zero_iff).mp hquot |>.resolve_right hellpos.ne'
  nlinarith

/-- Helper for eq:polar-family: the scalar formula defining `baseDeltaEven`. -/
theorem baseDeltaEven_def (ell z : ℝ) : baseDeltaEven ell z = ell - 1 + z := by
  rfl

/-- Helper for eq:polar-family: the scalar formula defining `baseDeltaOdd`. -/
theorem baseDeltaOdd_def (ell z : ℝ) : baseDeltaOdd ell z = 1 - ell + z * ell := by
  rfl

/-- Helper for eq:polar-family: the scalar formula defining `baseGamma`. -/
theorem baseGamma_def (ell z : ℝ) : baseGamma ell z = 1 / (z * ell) := by
  rfl

/-- Helper for eq:polar-family: the scalar formula defining `baseKappa`. -/
theorem baseKappa_def (ell z : ℝ) : baseKappa ell z = (1 - z / ell) * (1 - z * ell) := by
  rfl

/-- Helper for eq:polar-family: the scalar formula defining `curvatureEven`. -/
theorem curvatureEven_def (ell z : ℝ) : curvatureEven ell z = 1 / (ell + z) := by
  rfl

/-- Helper for eq:polar-family: the scalar formula defining `curvatureOdd`. -/
theorem curvatureOdd_def (ell z : ℝ) : curvatureOdd ell z = ell / (1 + z * ell) := by
  rfl

/-- Helper for eq:polar-family: the difference defining the base family parameter. -/
theorem baseNu_def (ell : ℝ) : baseNu ell = ell - 1 := by
  rfl



/-- Helper for eq:polar-two-cycle: the rational even state has its source coefficients. -/
theorem evenState_def (δE δO ν : ℝ) :
    evenState δE δO ν = cycleState (cycleGamma δE δO ν) (cycleLambdaEven δE δO ν) := by
  rfl

/-- Helper for eq:polar-two-cycle: the rational odd state has its source coefficients. -/
theorem oddState_def (δE δO ν : ℝ) :
    oddState δE δO ν = cycleState (cycleGamma δE δO ν) (cycleLambdaOdd δE δO ν) := by
  rfl

end DFP.Polar.General
