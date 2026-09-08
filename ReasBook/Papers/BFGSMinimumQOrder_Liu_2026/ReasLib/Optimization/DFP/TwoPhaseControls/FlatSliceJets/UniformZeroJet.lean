module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformAt

public section

noncomputable section

open scoped BigOperators

namespace FiniteTaylorJet

universe u v

variable {Θ : Type u} {F : Type v}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A jointly `C⁵` scalar-path family whose order-four jets vanish has a
uniform fifth-order norm bound on every compact parameter set. -/
theorem uniform_orderFive_bound_of_zero_fourJet
    (f : Θ → ℝ → F) (K : Set Θ) (hK : IsCompact K)
    (hf : ∀ θ ∈ K,
      ContDiffAt ℝ 5 (Function.uncurry f) (θ, (0 : ℝ)))
    (hzero : ∀ θ ∈ K,
      ofFunction ℝ 4 (f θ) 0 =
        ofFunction ℝ 4 (fun _ : ℝ => (0 : F)) 0) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ ε : ℝ, |ε| < δ →
      ‖f θ ε‖ ≤ C * |ε| ^ (5 : ℕ) := by
  have hdata := uniformJetData_of_contDiffAt 5 f 0 K hK hf
  let top : Fin 6 := ⟨5, by omega⟩
  obtain ⟨B, hB, hcoeff⟩ := hdata.1 top
  have hrem := hdata.2 1 zero_lt_one
  obtain ⟨δ, hδ, hbound⟩ := hrem.bound
  refine ⟨B + 1, by linarith, δ, hδ, ?_⟩
  intro θ hθ ε hε
  let J5 : FiniteTaylorJet ℝ ℝ F 5 := ofFunction ℝ 5 (f θ) 0
  have heval : J5.eval ε = J5.coeff top (fun _ => ε) := by
    rw [eval_eq_sum]
    apply Finset.sum_eq_single top
    · intro n hn hntop
      have hnlt : (n : ℕ) < 5 := by
        have hnne : (n : ℕ) ≠ 5 := by
          intro hn
          apply hntop
          apply Fin.ext
          simpa only [top] using hn
        omega
      let n4 : Fin 5 := ⟨n, hnlt⟩
      have hz4 :
          (ofFunction ℝ 4 (f θ) 0).coeff n4 = 0 := by
        have hz := congrArg
          (fun J : FiniteTaylorJet ℝ ℝ F 4 => J.coeff n4)
          (hzero θ hθ)
        simpa only [coeff_ofFunction, iteratedFDeriv_fun_zero,
          Pi.zero_apply, smul_zero] using hz
      have hz5 : J5.coeff n = 0 := by
        dsimp only [J5]
        simpa only [coeff_ofFunction] using hz4
      rw [hz5]
      exact zero_apply _
    · simp
  have htop :
      ‖J5.coeff top (fun _ => ε)‖ ≤ B * |ε| ^ (5 : ℕ) := by
    calc
      ‖J5.coeff top (fun _ => ε)‖
          ≤ ‖J5.coeff top‖ * ∏ _i : Fin 5, ‖ε‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖J5.coeff top‖ * |ε| ^ (5 : ℕ) := by
        simp only [Finset.prod_const, Finset.card_fin, Real.norm_eq_abs]
      _ ≤ B * |ε| ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right (hcoeff θ hθ) (pow_nonneg (abs_nonneg ε) 5)
  have hremBound :
      ‖J5.remainder (f θ) 0 ε‖ ≤ |ε| ^ (5 : ℕ) := by
    have h := hbound θ hθ ε
    have hnorm : ‖ε‖ < δ := by
      simpa only [Real.norm_eq_abs] using hε
    have := h hnorm
    simpa only [J5, one_mul, Real.norm_eq_abs, Real.rpow_natCast] using this
  have hdecomp :
      f θ ε = J5.remainder (f θ) 0 ε + J5.eval ε := by
    rw [remainder_def]
    simp only [zero_add]
    abel
  rw [hdecomp, heval]
  calc
    ‖J5.remainder (f θ) 0 ε + J5.coeff top (fun _ => ε)‖
        ≤ ‖J5.remainder (f θ) 0 ε‖ + ‖J5.coeff top (fun _ => ε)‖ :=
      norm_add_le _ _
    _ ≤ |ε| ^ (5 : ℕ) + B * |ε| ^ (5 : ℕ) :=
      add_le_add hremBound htop
    _ = (B + 1) * |ε| ^ (5 : ℕ) := by ring

end FiniteTaylorJet
