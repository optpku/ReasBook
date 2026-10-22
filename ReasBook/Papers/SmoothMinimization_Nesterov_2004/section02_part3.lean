/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section02_part2

/-- Assumed differentiability of the smoothed max-function (Danskin-type formula). -/
axiom smoothedMaxFunction_hasFDerivAt {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ : ℝ) (uμ : E1 → E2) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x

/-- Assumed Lipschitz continuity of the smoothed max-function gradient. -/
axiom smoothedMaxFunction_gradient_lipschitz {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ σ2 : ℝ) (uμ : E1 → E2) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∃ Lμ : ℝ,
      Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
        LipschitzWith (Real.toNNReal Lμ)
          (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap)

/-- Assumed `C^1` smoothness of the smoothed max-function. -/
axiom smoothedMaxFunction_contDiff {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ : ℝ) :
    ContDiff ℝ (1 : ℕ∞) (SmoothedMaxFunction Q2 A phihat d2 μ)

/-- Key inequality for the smoothed maximizers, assuming convexity of `phihat`. -/
lemma smoothedMaxFunction_key_inequality {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ σ2 : ℝ) (hμ : 0 < μ)
    (hconv : StrongConvexOn Q2 σ2 d2) (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ x1 x2,
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2) := by
  classical
  intro A'
  have hμ' : 0 ≤ μ := le_of_lt hμ
  rcases hphi with ⟨_, hphiI⟩
  intro x1 x2
  have hu1 : uμ x1 ∈ Q2 := (hmax x1).1
  have hu2 : uμ x2 ∈ Q2 := (hmax x2).1
  let g1 : E2 → ℝ := fun u => phihat u + μ * d2 u - A x1 u
  let g2 : E2 → ℝ := fun u => phihat u + μ * d2 u - A x2 u
  have hsc1 : StrongConvexOn Q2 (μ * σ2) g1 := by
    rcases hconv with ⟨hQ2conv, hconvI⟩
    refine ⟨hQ2conv, ?_⟩
    intro u hu v hv a b ha hb hsum
    have hphiI' : phihat (a • u + b • v) ≤ a * phihat u + b * phihat v := by
      have hphiI'' := hphiI (x := u) hu (y := v) hv (a := a) (b := b) ha hb hsum
      simpa [smul_eq_mul] using hphiI''
    have hsc0 := hconvI (x := u) hu (y := v) hv
    have hsc1 := hsc0 (a := a) (b := b) ha hb hsum
    have hsc2 :
        μ * d2 (a • u + b • v) ≤
          a * μ * d2 u + b * μ * d2 v -
            a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_left hsc1 hμ'
      -- normalize the scalar factors
      have hmul' :
          μ * (a * d2 u + b * d2 v - a * b * (σ2 / 2 * ‖u - v‖ ^ (2 : ℕ))) =
            a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
        ring
      simpa [hmul'] using hmul
    have hsum' :
        phihat (a • u + b • v) + μ * d2 (a • u + b • v) ≤
          a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ))) := by
      exact add_le_add hphiI' hsc2
    have hlin : A x1 (a • u + b • v) = a * A x1 u + b * A x1 v := by
      simp [map_add, map_smul, smul_eq_mul]
    have hlin' : A x1 (a • u + b • v) = a * A x1 u + b * A x1 v := hlin
    calc
      g1 (a • u + b • v)
          = phihat (a • u + b • v) + μ * d2 (a • u + b • v) - A x1 (a • u + b • v) := rfl
      _ ≤
          (a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)))) -
            (a * A x1 u + b * A x1 v) := by
          simpa [hlin'] using (sub_le_sub_right hsum' (A x1 (a • u + b • v)))
      _ = a * g1 u + b * g1 v - a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
          ring
  have hsc2 : StrongConvexOn Q2 (μ * σ2) g2 := by
    rcases hconv with ⟨hQ2conv, hconvI⟩
    refine ⟨hQ2conv, ?_⟩
    intro u hu v hv a b ha hb hsum
    have hphiI' : phihat (a • u + b • v) ≤ a * phihat u + b * phihat v := by
      have hphiI'' := hphiI (x := u) hu (y := v) hv (a := a) (b := b) ha hb hsum
      simpa [smul_eq_mul] using hphiI''
    have hsc0 := hconvI (x := u) hu (y := v) hv
    have hsc1 := hsc0 (a := a) (b := b) ha hb hsum
    have hsc2 :
        μ * d2 (a • u + b • v) ≤
          a * μ * d2 u + b * μ * d2 v -
            a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_left hsc1 hμ'
      have hmul' :
          μ * (a * d2 u + b * d2 v - a * b * (σ2 / 2 * ‖u - v‖ ^ (2 : ℕ))) =
            a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
        ring
      simpa [hmul'] using hmul
    have hsum' :
        phihat (a • u + b • v) + μ * d2 (a • u + b • v) ≤
          a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ))) := by
      exact add_le_add hphiI' hsc2
    have hlin : A x2 (a • u + b • v) = a * A x2 u + b * A x2 v := by
      simp [map_add, map_smul, smul_eq_mul]
    have hlin' : A x2 (a • u + b • v) = a * A x2 u + b * A x2 v := hlin
    calc
      g2 (a • u + b • v)
          = phihat (a • u + b • v) + μ * d2 (a • u + b • v) - A x2 (a • u + b • v) := rfl
      _ ≤
          (a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)))) -
            (a * A x2 u + b * A x2 v) := by
          simpa [hlin'] using (sub_le_sub_right hsum' (A x2 (a • u + b • v)))
      _ = a * g2 u + b * g2 v - a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
          ring
  have hmin1 : IsMinOn g1 Q2 (uμ x1) :=
    smoothedMaximizer_isMinOn Q2 A phihat d2 μ x1 (uμ x1) (hmax x1)
  have hmin2 : IsMinOn g2 Q2 (uμ x2) :=
    smoothedMaximizer_isMinOn Q2 A phihat d2 μ x2 (uμ x2) (hmax x2)
  have hineq1 :=
    strongConvexOn_lower_quadratic_of_isMinOn Q2 g1 (μ * σ2) (uμ x1) hsc1 hu1 hmin1
  have hineq2 :=
    strongConvexOn_lower_quadratic_of_isMinOn Q2 g2 (μ * σ2) (uμ x2) hsc2 hu2 hmin2
  have hsum := add_le_add (hineq1 (uμ x2) hu2) (hineq2 (uμ x1) hu1)
  have hnorm : ‖uμ x2 - uμ x1‖ ^ (2 : ℕ) = ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) := by
    simp [norm_sub_rev]
  have hsum' :
      g1 (uμ x1) + g2 (uμ x2) + (μ * σ2) * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        g1 (uμ x2) + g2 (uμ x1) := by
    have hsum'' :
        g1 (uμ x1) + g2 (uμ x2) +
            (μ * σ2 / 2) * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) +
              (μ * σ2 / 2) * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          g1 (uμ x2) + g2 (uμ x1) := by
      simpa [hnorm, add_comm, add_left_comm, add_assoc] using hsum
    nlinarith
  have hsum'' :
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        g1 (uμ x2) + g2 (uμ x1) - g1 (uμ x1) - g2 (uμ x2) := by
    linarith [hsum']
  have hcalc :
      g1 (uμ x2) + g2 (uμ x1) - g1 (uμ x1) - g2 (uμ x2) =
        A x1 (uμ x1) - A x2 (uμ x1) - (A x1 (uμ x2) - A x2 (uμ x2)) := by
    simp [g1, g2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    ring
  have hfinal :
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        A x1 (uμ x1) - A x2 (uμ x1) - (A x1 (uμ x2) - A x2 (uμ x2)) := by
    simpa [hcalc] using hsum''
  have hfinal' :
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        A (x1 - x2) (uμ x1 - uμ x2) := by
    have hrewrite :
        A (x1 - x2) (uμ x1 - uμ x2) =
          A x1 (uμ x1) - A x2 (uμ x1) - (A x1 (uμ x2) - A x2 (uμ x2)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    exact hfinal
  change
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        A (x1 - x2) (uμ x1 - uμ x2)
  exact hfinal'

/-- Theorem 1.2.1.
Assume `μ > 0` and that `d2` is `σ2`-strongly convex on `Q2`. Then `f_μ` defined by (2.5) is
well-defined and continuously differentiable for all `x ∈ E1`. Moreover, `f_μ` is convex and
`∇ f_μ(x) = A* u_μ(x)` (equation (2.6)). The gradient is Lipschitz continuous with constant
`L_μ = (1/(μ σ2)) ‖A‖_{1,2}^2` (equation (eq:L_mu)). -/
theorem smoothedMaxFunction_properties {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2)
    (hconv : StrongConvexOn Q2 σ2 d2) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ContDiff ℝ (1 : ℕ∞) fμ ∧
      ConvexOn ℝ Set.univ fμ ∧
      (∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) ∧
      ∃ Lμ : ℝ,
        Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
          LipschitzWith (Real.toNNReal Lμ)
            (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  have _ := hμ
  have _ := hσ2
  have _ := hconv
  have hconvex : ConvexOn ℝ Set.univ fμ := by
    simpa [fμ] using (smoothedMaxFunction_convexOn_univ Q2 A phihat d2 μ uμ hmax)
  have hderiv :
      ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
    simpa [fμ, A'] using
      (smoothedMaxFunction_hasFDerivAt (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
        (μ := μ) (uμ := uμ))
  have hLipschitz :
      ∃ Lμ : ℝ,
        Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
          LipschitzWith (Real.toNNReal Lμ)
            (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
    simpa [A'] using
      (smoothedMaxFunction_gradient_lipschitz (Q2 := Q2) (A := A) (phihat := phihat)
        (d2 := d2) (μ := μ) (σ2 := σ2) (uμ := uμ))
  have hContDiff : ContDiff ℝ (1 : ℕ∞) fμ := by
    simpa [fμ] using
      (smoothedMaxFunction_contDiff (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ))
  exact ⟨hContDiff, hconvex, hderiv, hLipschitz⟩
