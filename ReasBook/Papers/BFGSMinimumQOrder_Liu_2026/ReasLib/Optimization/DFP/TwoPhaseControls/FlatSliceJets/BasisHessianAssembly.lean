module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.HessianAssembly

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg

private theorem bilinear_add_right
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E [×2]→L[ℝ] F) (x y z : E) :
    A ![x, y + z] = A ![x, y] + A ![x, z] := by
  have hupdate (w : E) : Function.update ![x, 0] (1 : Fin 2) w = ![x, w] := by
    funext i
    fin_cases i <;> simp
  have h := A.map_update_add ![x, 0] (1 : Fin 2) y z
  simpa only [hupdate] using h

private theorem bilinear_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E [×2]→L[ℝ] F) (c d : ℝ) (x y : E) :
    A ![c • x, d • y] = (c * d) • A ![x, y] := by
  have h := A.map_smul_univ ![c, d] ![x, y]
  have hprod : (∏ i : Fin 2, ![c, d] i) = c * d := by
    rw [Fin.prod_univ_two]
    rfl
  rw [hprod] at h
  calc
    A ![c • x, d • y] = A (fun i => ![c, d] i • ![x, y] i) := by
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = (c * d) • A ![x, y] := h

private theorem cross_of_basis
    (f : (ℝ × ℝ × ℝ) → ℝ) (P H : ℝ)
    (hP :
      iteratedFDeriv ℝ 2 f (0, 2, 1)
        ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 1, 0)] = 0)
    (hH :
      iteratedFDeriv ℝ 2 f (0, 2, 1)
        ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 0, 1)] = 0) :
    iteratedFDeriv ℝ 2 f (0, 2, 1)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, P, H)] = 0 := by
  let A := iteratedFDeriv ℝ 2 f ((0, 2, 1) : ℝ × ℝ × ℝ)
  let u : ℝ × ℝ × ℝ := (1, 0, 0)
  let eP : ℝ × ℝ × ℝ := (0, 1, 0)
  let eH : ℝ × ℝ × ℝ := (0, 0, 1)
  have hv : ((0, P, H) : ℝ × ℝ × ℝ) = P • eP + H • eH := by
    ext <;> simp [eP, eH]
  have hPsmul : A ![u, P • eP] = P • A ![u, eP] := by
    simpa only [one_mul, one_smul] using bilinear_smul A 1 P u eP
  have hHsmul : A ![u, H • eH] = H • A ![u, eH] := by
    simpa only [one_mul, one_smul] using bilinear_smul A 1 H u eH
  change A ![u, (0, P, H)] = 0
  rw [hv, bilinear_add_right, hPsmul, hHsmul]
  change P • (iteratedFDeriv ℝ 2 f (0, 2, 1)) ![(1, 0, 0), (0, 1, 0)] +
      H • (iteratedFDeriv ℝ 2 f (0, 2, 1)) ![(1, 0, 0), (0, 0, 1)] = 0
  rw [hP, hH, smul_zero, smul_zero, add_zero]

/-- Basis-direction version of `weightedNormalizedRadiusJet_of_scale_and_cross`.
The two Hessian assumptions are independent of the graph coefficients. -/
theorem weightedNormalizedRadiusJet_of_scale_and_basis_cross
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => radiusFactor ε 2 1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 1 - (300 / 18) * ε ^ 3 + (54 / 18) * ε ^ 4) 0)
    (hcrossP :
      iteratedFDeriv ℝ 2
          (fun x : ℝ × ℝ × ℝ => radiusFactor x.1 x.2.1 x.2.2)
          (0, 2, 1) ![(1, 0, 0), (0, 1, 0)] = 0)
    (hcrossH :
      iteratedFDeriv ℝ 2
          (fun x : ℝ × ℝ × ℝ => radiusFactor x.1 x.2.1 x.2.2)
          (0, 2, 1) ![(1, 0, 0), (0, 0, 1)] = 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          radiusFactor ε
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
            ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0 :=
  weightedNormalizedRadiusJet_of_scale_and_cross P₃ H₃ P₄ H₄ hscale
    (cross_of_basis _ P₃ H₃ hcrossP hcrossH)

/-- Basis-direction version of `weightedTransversePJet_of_scale_and_cross`.
The two Hessian assumptions are independent of the graph coefficients. -/
theorem weightedTransversePJet_of_scale_and_basis_cross
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4) 0)
    (hcrossP :
      iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ => (stateMap x).2.1)
          (0, 2, 1) ![(1, 0, 0), (0, 1, 0)] = 0)
    (hcrossH :
      iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ => (stateMap x).2.1)
          (0, 2, 1) ![(1, 0, 0), (0, 0, 1)] = 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0 :=
  weightedTransversePJet_of_scale_and_cross P₃ H₃ P₄ H₄ hscale
    (cross_of_basis _ P₃ H₃ hcrossP hcrossH)

/-- Basis-direction version of `weightedTransverseHJet_of_scale_and_cross`.
The two Hessian assumptions are independent of the graph coefficients. -/
theorem weightedTransverseHJet_of_scale_and_basis_cross
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0)
    (hcrossP :
      iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ => (stateMap x).2.2)
          (0, 2, 1) ![(1, 0, 0), (0, 1, 0)] = 0)
    (hcrossH :
      iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ => (stateMap x).2.2)
          (0, 2, 1) ![(1, 0, 0), (0, 0, 1)] = 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 :=
  weightedTransverseHJet_of_scale_and_cross P₃ H₃ P₄ H₄ hscale
    (cross_of_basis _ P₃ H₃ hcrossP hcrossH)

end DFP.TwoLeg
