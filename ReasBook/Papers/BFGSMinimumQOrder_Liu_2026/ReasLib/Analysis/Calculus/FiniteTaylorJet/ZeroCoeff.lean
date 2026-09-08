module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations

public section

universe u v w

namespace FiniteTaylorJet

variable {𝕜 : Type u} {E : Type v} {F : Type w}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The degree-zero coefficient evaluated on its unique zero input is the constant coefficient.
This explicit `Fin 0` form is useful when a coefficient equality is transported through an
extensionality proof. -/
theorem coeff_zero_apply_zero_eq_constantCoeff {m : ℕ}
    (J : FiniteTaylorJet 𝕜 E F m) :
    J.coeff (0 : Fin (m + 1)) (fun _ : Fin 0 ↦ (0 : E)) = J.constantCoeff := by
  exact (constantCoeff_eq_coeff_zero J).symm

/-- Equality of constant coefficients can be checked by evaluating both degree-zero coefficients
on their explicit `Fin 0` zero input. -/
theorem constantCoeff_eq_of_coeff_zero_apply_zero_eq {m : ℕ}
    {J K : FiniteTaylorJet 𝕜 E F m}
    (h : J.coeff (0 : Fin (m + 1)) (fun _ : Fin 0 ↦ (0 : E)) =
      K.coeff (0 : Fin (m + 1)) (fun _ : Fin 0 ↦ (0 : E))) :
    J.constantCoeff = K.constantCoeff := by
  calc
    J.constantCoeff = J.coeff (0 : Fin (m + 1)) (fun _ : Fin 0 ↦ (0 : E)) :=
      (coeff_zero_apply_zero_eq_constantCoeff J).symm
    _ = K.coeff (0 : Fin (m + 1)) (fun _ : Fin 0 ↦ (0 : E)) := h
    _ = K.constantCoeff := coeff_zero_apply_zero_eq_constantCoeff K

end FiniteTaylorJet
