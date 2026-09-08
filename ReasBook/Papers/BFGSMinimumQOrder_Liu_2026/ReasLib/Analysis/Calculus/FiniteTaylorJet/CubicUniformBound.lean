module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform

public section

/-!
# Uniform cubic bounds from finite Taylor jets

A uniform order-three jet whose first three coefficients vanish gives a uniform cubic
bound for the underlying scalar-input family.  This packages the Taylor estimate needed
by transverse-factor and graph-transform arguments without introducing a divided quotient.
-/

open Filter
open scoped BigOperators Topology

universe u v

namespace FiniteTaylorJet

variable {Theta : Type u} {F : Type v}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Infrastructure I.16 (Finite-smooth invariant graph under an explicit stable contraction):
a uniform order-three scalar jet whose coefficients of degrees zero, one, and two vanish
is uniformly bounded by a constant times `‖h ^ 3‖`.  The same estimate supplies the
cubic transverse-factor bound required by Lemma 4.15. -/
theorem IsUniformOn.exists_cubic_bound_of_coeff_zero
    {f : Theta → ℝ → F} {J : Theta → FiniteTaylorJet ℝ ℝ F 3}
    {K : Set Theta}
    (hJ : FiniteTaylorJet.IsUniformOn f J 0 K)
    (hzero : ∀ theta ∈ K, ∀ n : Fin 4, (n : ℕ) < 3 → (J theta).coeff n = 0) :
    ∃ C > 0, ∃ delta > 0, ∀ theta ∈ K, ∀ h : ℝ, ‖h‖ < delta →
      ‖f theta h‖ ≤ C * ‖h ^ (3 : ℕ)‖ := by
  obtain ⟨B, hB, htopCoeff⟩ := hJ.boundedCoeff (3 : Fin 4)
  obtain ⟨delta, hdelta, hremainder⟩ :=
    IsUniformRemainderOn.bound (hJ.remainder 1 zero_lt_one)
  have hzeroLt : (0 : ℕ) < 3 := by
    norm_num
  have honeLt : (1 : ℕ) < 3 := by
    norm_num
  have htwoLt : (2 : ℕ) < 3 := by
    norm_num
  have hCubic : 0 < B + 1 := by
    linarith
  refine ⟨B + 1, hCubic, delta, hdelta, ?_⟩
  intro theta htheta h hh
  have heval : (J theta).eval h =
      (J theta).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ h) := by
    rw [eval_eq_sum, Fin.sum_univ_four,
      hzero theta htheta (0 : Fin 4) hzeroLt,
      hzero theta htheta (1 : Fin 4) honeLt,
      hzero theta htheta (2 : Fin 4) htwoLt]
    simp only [zero_apply, zero_add]
    rfl
  have htop : ‖(J theta).eval h‖ ≤ B * ‖h ^ (3 : ℕ)‖ := by
    rw [heval]
    calc
      ‖(J theta).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ h)‖ ≤
          ‖(J theta).coeff (3 : Fin 4)‖ *
            ∏ _i : Fin 3, ‖h‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ B * ∏ _i : Fin 3, ‖h‖ :=
        mul_le_mul_of_nonneg_right (htopCoeff theta htheta)
          (Finset.prod_nonneg fun _ _ ↦ norm_nonneg h)
      _ = B * ‖h ^ (3 : ℕ)‖ := by
        simp only [Finset.prod_const, Finset.card_fin, norm_pow]
  have hrem : ‖(J theta).remainder (f theta) 0 h‖ ≤ ‖h ^ (3 : ℕ)‖ := by
    have hbound := hremainder theta htheta h hh
    simpa only [Real.rpow_natCast, one_mul, norm_pow] using hbound
  have hvalue : f theta h =
      (J theta).remainder (f theta) 0 h + (J theta).eval h := by
    rw [remainder_def, zero_add]
    abel
  rw [hvalue]
  calc
    ‖(J theta).remainder (f theta) 0 h + (J theta).eval h‖ ≤
        ‖(J theta).remainder (f theta) 0 h‖ + ‖(J theta).eval h‖ :=
      norm_add_le _ _
    _ ≤ ‖h ^ (3 : ℕ)‖ + B * ‖h ^ (3 : ℕ)‖ :=
      add_le_add hrem htop
    _ = (B + 1) * ‖h ^ (3 : ℕ)‖ := by
      ring

/-- Helper for Infrastructure I.16 (Finite-smooth invariant graph under an explicit stable
contraction): a uniform cubic estimate on a parameter neighborhood becomes an eventual
estimate on the product neighborhood of `(0, theta0)`. -/
theorem IsUniformOn.eventually_cubic_bound_of_coeff_zero
    [TopologicalSpace Theta]
    {f : Theta → ℝ → F} {J : Theta → FiniteTaylorJet ℝ ℝ F 3}
    {K : Set Theta} {theta0 : Theta}
    (hJ : FiniteTaylorJet.IsUniformOn f J 0 K) (hK : K ∈ 𝓝 theta0)
    (hzero : ∀ theta ∈ K, ∀ n : Fin 4, (n : ℕ) < 3 → (J theta).coeff n = 0) :
    ∃ C > 0, ∀ᶠ x : ℝ × Theta in 𝓝 (0, theta0),
      ‖f x.2 x.1‖ ≤ C * ‖x.1 ^ (3 : ℕ)‖ := by
  obtain ⟨C, hC, delta, hdelta, hbound⟩ :=
    hJ.exists_cubic_bound_of_coeff_zero hzero
  have hfst : Tendsto (fun x : ℝ × Theta ↦ x.1)
      (𝓝 (0, theta0)) (𝓝 0) := continuousAt_fst
  have hsnd : Tendsto (fun x : ℝ × Theta ↦ x.2)
      (𝓝 (0, theta0)) (𝓝 theta0) := continuousAt_snd
  have hsmall : ∀ᶠ x : ℝ × Theta in 𝓝 (0, theta0),
      x.1 ∈ Metric.ball (0 : ℝ) delta :=
    hfst.eventually (Metric.ball_mem_nhds (0 : ℝ) hdelta)
  have hparameter : ∀ᶠ x : ℝ × Theta in 𝓝 (0, theta0), x.2 ∈ K :=
    hsnd.eventually hK
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsmall, hparameter] with x hx htheta
  have hxNorm : ‖x.1‖ < delta := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  exact hbound x.2 htheta x.1 hxNorm

end FiniteTaylorJet
