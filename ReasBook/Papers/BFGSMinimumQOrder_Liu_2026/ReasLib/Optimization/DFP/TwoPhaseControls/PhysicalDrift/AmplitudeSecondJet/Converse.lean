module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
public import ReasLib.Analysis.Calculus.ContDiff.CubicVanishing
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion supplies the converse direction for the scalar quadratic-germ API.
The existing `HasQuadraticGerm.iteratedDeriv_two_eq_of_contDiffAt` reads a germ into
the second derivative; the theorem below reconstructs the germ from the three Taylor
coefficients.  It is deliberately independent of the mixed-map evaluator.
-/

/- The derivative identities for the quadratic model are kept as named interface facts,
   so downstream germ proofs do not unfold the model in their main argument. -/

/-- Helper for Appendix Lemma A.6: the derivative of a quadratic model at the origin is
    its linear coefficient. -/
theorem quadraticModel_deriv_at_zero (a₀ a₁ a₂ : ℝ) :
    deriv (quadraticModel a₀ a₁ a₂) 0 = a₁ := by
  have hlinear := (hasDerivAt_const (0 : ℝ) a₀).add
    ((hasDerivAt_const (0 : ℝ) a₁).mul (hasDerivAt_id (0 : ℝ)))
  have hquadratic :=
    (hasDerivAt_const (0 : ℝ) a₂).mul ((hasDerivAt_id (0 : ℝ)).pow 2)
  have hsum := hlinear.add hquadratic
  have hcoeff :
      0 + (0 * id 0 + a₁ * 1) +
        (0 * (id ^ 2) 0 + a₂ * ((2 : ℝ) * id 0 ^ (2 - 1) * 1)) = a₁ := by
    simp [id]
  have hsum' := hsum.congr_deriv hcoeff
  have hfunction :
      (fun x : ℝ ↦ a₀) + (fun x ↦ a₁) * id + (fun x ↦ a₂) * id ^ 2 =
        quadraticModel a₀ a₁ a₂ := by
    funext r
    simp [quadraticModel]
  rw [hfunction] at hsum'
  exact hsum'.deriv

/-- Helper for Appendix Lemma A.6: the second iterated derivative of a quadratic model
    at the origin is twice its quadratic coefficient. -/
theorem quadraticModel_iteratedDeriv_two_at_zero (a₀ a₁ a₂ : ℝ) :
    iteratedDeriv 2 (quadraticModel a₀ a₁ a₂) 0 = 2 * a₂ := by
  have hmodelDeriv :
      deriv (quadraticModel a₀ a₁ a₂) = fun r ↦ a₁ + 2 * a₂ * r := by
    funext r
    have hlinear := (hasDerivAt_const r a₁).mul (hasDerivAt_id r)
    have hquadratic := (hasDerivAt_const r a₂).mul ((hasDerivAt_id r).pow 2)
    have hsum := (hasDerivAt_const r a₀).add (hlinear.add hquadratic)
    have hcoeff :
        0 + (0 * id r + a₁ * 1 +
          (0 * (id ^ 2) r + a₂ * ((2 : ℝ) * id r ^ (2 - 1) * 1))) =
          a₁ + 2 * a₂ * r := by
      simp [id]
      ring
    have hsum' := hsum.congr_deriv hcoeff
    have hfunction :
        (fun x : ℝ ↦ a₀) + ((fun x ↦ a₁) * id + (fun x ↦ a₂) * id ^ 2) =
          quadraticModel a₀ a₁ a₂ := by
      funext s
      simp [quadraticModel]
      ring
    rw [hfunction] at hsum'
    exact hsum'.deriv
  have hlinear : HasDerivAt (fun r : ℝ ↦ a₁ + 2 * a₂ * r) (2 * a₂) 0 := by
    have hraw := (hasDerivAt_const (0 : ℝ) a₁).add
      ((hasDerivAt_const (0 : ℝ) (2 * a₂)).mul (hasDerivAt_id (0 : ℝ)))
    apply hraw.congr_deriv
    simp
  calc
    iteratedDeriv 2 (quadraticModel a₀ a₁ a₂) 0 =
        deriv (deriv (quadraticModel a₀ a₁ a₂)) 0 := by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    _ = deriv (fun r ↦ a₁ + 2 * a₂ * r) 0 := by rw [hmodelDeriv]
    _ = 2 * a₂ := hlinear.deriv

/-- Appendix Lemma A.6 companion: a `C³` scalar path with prescribed value, first
    derivative, and second iterated derivative has the corresponding quadratic germ. -/
theorem HasQuadraticGerm.of_contDiffAt_iteratedDeriv_two
    {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hregular : ContDiffAt ℝ 3 f 0)
    (hzero : f 0 = a₀)
    (hfirst : deriv f 0 = a₁)
    (hsecond : iteratedDeriv 2 f 0 = 2 * a₂) :
    HasQuadraticGerm f a₀ a₁ a₂ := by
  let q : ℝ → ℝ := quadraticModel a₀ a₁ a₂
  have hqregular : ContDiffAt ℝ 3 q 0 := by
    unfold q
    unfold quadraticModel
    fun_prop
  have hqzero : q 0 = a₀ := by
    dsimp [q]
    simp [quadraticModel]
  have hqfirst : deriv q 0 = a₁ := by
    simpa only [q] using quadraticModel_deriv_at_zero a₀ a₁ a₂
  have hqsecond : iteratedDeriv 2 q 0 = 2 * a₂ := by
    simpa only [q] using quadraticModel_iteratedDeriv_two_at_zero a₀ a₁ a₂
  let h : ℝ → ℝ := fun r ↦ f r - q r
  have hregular' : ContDiffAt ℝ 3 h 0 := by
    exact hregular.sub hqregular
  have horder1 : (1 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  have horder2 : (2 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  have hzeroDeriv : ∀ n < 3, iteratedDeriv n h 0 = 0 := by
    intro n hn
    interval_cases n
    · simp only [iteratedDeriv_zero]
      change f 0 - q 0 = 0
      rw [hzero, hqzero]
      simp
    · have hregular1 : ContDiffAt ℝ 1 f 0 := hregular.of_le horder1
      have hqregular1 : ContDiffAt ℝ 1 q 0 := hqregular.of_le horder1
      have hsub : iteratedDeriv 1 (f - q) 0 =
          iteratedDeriv 1 f 0 - iteratedDeriv 1 q 0 :=
        iteratedDeriv_sub hregular1 hqregular1
      have hfun : h = f - q := by
        funext r
        rfl
      rw [hfun]
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hfirst, hqfirst,
        sub_self] using hsub
    · have hregular2 : ContDiffAt ℝ 2 f 0 := hregular.of_le horder2
      have hqregular2 : ContDiffAt ℝ 2 q 0 := hqregular.of_le horder2
      have hsub : iteratedDeriv 2 (f - q) 0 =
          iteratedDeriv 2 f 0 - iteratedDeriv 2 q 0 :=
        iteratedDeriv_sub hregular2 hqregular2
      have hfun : h = f - q := by
        funext r
        rfl
      rw [hfun]
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hsecond, hqsecond,
        sub_self] using hsub
  have hbound := ContDiffAt.isBigO_of_threefold_vanishing hregular' hzeroDeriv
  have hbound' :
      (fun r : ℝ ↦ f r - quadraticModel a₀ a₁ a₂ r) =O[𝓝 0]
        (fun r ↦ r ^ (3 : ℕ)) := by
    refine hbound.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [] with r
    simp only [h, q, zero_add]
  have hEq : EqModPow 3 f (quadraticModel a₀ a₁ a₂) := by
    exact EqModPow.of_isBigO hbound'
  exact ⟨hregular.continuousAt, hEq⟩

/-- Helper for Appendix Lemma A.6: under `C³` regularity, a quadratic germ exposes
    its value, first derivative, and second iterated derivative at the base point. -/
theorem HasQuadraticGerm.iteratedDeriv_coefficients_of_contDiffAt
    {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hregular : ContDiffAt ℝ 3 f 0) :
    iteratedDeriv 0 f 0 = a₀ ∧
      iteratedDeriv 1 f 0 = a₁ ∧
        iteratedDeriv 2 f 0 = 2 * a₂ := by
  have hthree : 0 < (3 : ℕ) := by
    norm_num
  have htwoLeThree : (2 : ℕ) ≤ 3 := by
    norm_num
  have hzeroSquare : (0 : ℝ) ^ (2 : ℕ) = 0 := by
    norm_num
  have hzeroValue : f 0 = a₀ := by
    have hvalue := EqModPow.eq_at_zero_of_pos (n := 3)
      hthree hf.eqMod
    simpa only [quadraticModel, zero_mul, mul_zero, one_mul, add_zero, hzeroSquare] using hvalue
  have hfirstModel : deriv (quadraticModel a₀ a₁ a₂) 0 = a₁ := by
    exact quadraticModel_deriv_at_zero a₀ a₁ a₂
  have hfirstValue : iteratedDeriv 1 f 0 = a₁ := by
    have hmodelRegular : ContDiffAt ℝ 1 (quadraticModel a₀ a₁ a₂) 0 := by
      unfold quadraticModel
      fun_prop
    have hregularOrder : (1 : WithTop ENat) ≤ (3 : WithTop ENat) := by
      norm_num
    have hjet :
        FiniteTaylorJet.ofFunction ℝ 1 f 0 =
          FiniteTaylorJet.ofFunction ℝ 1 (quadraticModel a₀ a₁ a₂) 0 := by
      apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
        (hregular.of_le hregularOrder) hmodelRegular
      have hmodTwo := hf.eqMod.mono (n := 2) (m := 3)
        htwoLeThree
      simpa only [zero_add, Nat.reduceAdd] using hmodTwo.to_isBigO
    have hderivs :=
      (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 1 f
        (quadraticModel a₀ a₁ a₂) 0 0).mp hjet
    have hindex : (1 : ℕ) < 1 + 1 := by
      norm_num
    have hfirst := hderivs ⟨1, hindex⟩
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hfirstModel] using hfirst
  have hsecondValue := hf.iteratedDeriv_two_eq_of_contDiffAt hregular
  have hzeroIterated : iteratedDeriv 0 f 0 = a₀ := by
    simpa only [iteratedDeriv_zero] using hzeroValue
  exact ⟨hzeroIterated, hfirstValue, hsecondValue⟩

end DFP.TwoLeg.Mixed
