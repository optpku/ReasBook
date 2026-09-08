module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet

public section

universe u v

namespace FiniteTaylorJet

variable {𝕜 : Type u} {F : Type v}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A finite Taylor jet is determined coefficientwise. -/
@[ext] theorem ext_coeff {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {m : ℕ} {J K : FiniteTaylorJet 𝕜 E F m}
    (h : ∀ n, J.coeff n = K.coeff n) : J = K := by
  cases J with
  | mk Jcoeff =>
      cases K with
      | mk Kcoeff =>
          congr 1
          funext n
          exact h n

/-- Equality of finite Taylor jets is coefficientwise equality. -/
theorem eq_iff_coeff_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {m : ℕ} {J K : FiniteTaylorJet 𝕜 E F m} :
    J = K ↔ ∀ n, J.coeff n = K.coeff n := by
  constructor
  · rintro rfl n
    rfl
  · exact ext_coeff

/-- Two derivative-constructed one-variable jets agree exactly when their
iterated derivatives agree through the truncation order. -/
theorem ofFunction_eq_iff_iteratedDeriv_eq [CharZero 𝕜] (m : ℕ)
    (f g : 𝕜 → F) (x y : 𝕜) :
    ofFunction 𝕜 m f x = ofFunction 𝕜 m g y ↔
      ∀ n : Fin (m + 1),
        iteratedDeriv (n : ℕ) f x = iteratedDeriv (n : ℕ) g y := by
  constructor
  · intro h n
    have hcoeff := congrArg
      (fun J : FiniteTaylorJet 𝕜 𝕜 F m => J.scalarCoeff n) h
    rw [scalarCoeff_ofFunction, scalarCoeff_ofFunction] at hcoeff
    have hfactorial : (((n : ℕ).factorial : 𝕜)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n : ℕ))
    have hcancel := congrArg
      (fun z : F => ((n : ℕ).factorial : 𝕜) • z) hcoeff
    simpa only [smul_smul, mul_inv_cancel₀ hfactorial, one_smul] using hcancel
  · intro h
    apply ext_coeff
    intro n
    rw [coeff_ofFunction, coeff_ofFunction]
    congr 1
    apply ContinuousMultilinearMap.ext_ring
    simpa only [iteratedDeriv_eq_iteratedFDeriv] using h n

/-- The finite jet of a one-variable function is the zero-function jet exactly
when all iterated derivatives through the truncation order vanish. -/
theorem ofFunction_eq_zeroFunction_iff [CharZero 𝕜] (m : ℕ)
    (f : 𝕜 → F) (x : 𝕜) :
    ofFunction 𝕜 m f x = ofFunction 𝕜 m (fun _ => (0 : F)) x ↔
      ∀ n : Fin (m + 1), iteratedDeriv (n : ℕ) f x = 0 := by
  rw [ofFunction_eq_iff_iteratedDeriv_eq]
  simp

end FiniteTaylorJet
