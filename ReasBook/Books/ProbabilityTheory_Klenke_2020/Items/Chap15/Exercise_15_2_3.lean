/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

namespace Measure

/-- A real law is lattice distributed when it is concentrated on some affine lattice `a + d ℤ`. -/
def IsLatticeDistributed (μ : Measure ℝ) : Prop :=
  ∃ a d : ℝ, μ (Set.range fun n : ℤ ↦ a + (n : ℝ) * d) = 1

/-- Helper for Exercise 15.2.3: if `exp (u * x * I)` equals a fixed phase and `u ≠ 0`, then
`x` lies on the corresponding affine lattice with step `2 * π / u`. -/
lemma mem_affineIntLattice_of_exp_eq_phase {u x θ : ℝ} (hu : u ≠ 0)
    (h : Complex.exp (u * x * Complex.I) = Complex.exp (θ * Complex.I)) :
    x ∈ Set.range fun n : ℤ ↦ θ / u + (n : ℝ) * (2 * Real.pi / u) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  -- Taking imaginary parts isolates the real phase relation.
  have him : u * x = θ + (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, zero_add] at this
    simpa [two_mul, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have hx : x = (θ + (n : ℝ) * (2 * Real.pi)) / u := by
    apply (eq_div_iff hu).2
    calc
      x * u = u * x := by ring
      _ = θ + (n : ℝ) * (2 * Real.pi) := him
  calc
    θ / u + (n : ℝ) * (2 * Real.pi / u) = (θ + (n : ℝ) * (2 * Real.pi)) / u := by
      field_simp [hu]
    _ = x := hx.symm

/-- Helper for Exercise 15.2.3: if a probability law is concentrated on `a + d ℤ`, then every
frequency with period matching `d` evaluates its characteristic function to the phase at `a`. -/
lemma charFun_eq_phase_of_affineIntLattice (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a d u : ℝ} (hμ : μ (Set.range fun n : ℤ ↦ a + (n : ℝ) * d) = 1)
    (hperiod : Complex.exp (u * d * Complex.I) = 1) :
    charFun μ u = Complex.exp (u * a * Complex.I) := by
  let s : Set ℝ := Set.range fun n : ℤ ↦ a + (n : ℝ) * d
  have hs_meas : MeasurableSet s := (Set.countable_range _).measurableSet
  have hs_ae : ∀ᵐ x ∂μ, x ∈ s := (mem_ae_iff_prob_eq_one hs_meas).mpr hμ
  -- The support assumption makes the oscillatory integrand almost surely constant.
  have hconst :
      (fun x : ℝ ↦ Complex.exp (u * x * Complex.I)) =ᵐ[μ]
        fun _ ↦ Complex.exp (u * a * Complex.I) := by
    filter_upwards [hs_ae] with x hx
    rcases hx with ⟨n, rfl⟩
    have hvalue :
        Complex.exp (u * (a + (n : ℝ) * d) * Complex.I) = Complex.exp (u * a * Complex.I) := by
      have hsplit :
          (u * (a + (n : ℝ) * d) : ℂ) * Complex.I =
            (u * a : ℂ) * Complex.I + (n : ℂ) * ((u * d : ℂ) * Complex.I) := by
        simp [mul_add, mul_assoc, mul_left_comm, mul_comm]
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul, hperiod]
      simp
    simpa using hvalue
  rw [charFun_apply_real]
  calc
    ∫ x, Complex.exp (u * x * Complex.I) ∂μ
        = ∫ x, Complex.exp (u * a * Complex.I) ∂μ := integral_congr_ae hconst
    _ = Complex.exp (u * a * Complex.I) := by simp

/-- Helper for Exercise 15.2.3: if `‖charFun μ u‖ = 1` at some nonzero frequency `u`, then a
probability law `μ` is concentrated on an affine lattice with step `2 * π / u`. -/
lemma exists_affineIntLattice_of_norm_charFun_eq_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u ≠ 0) (hφ : ‖charFun μ u‖ = 1) :
    ∃ a : ℝ, μ (Set.range fun n : ℤ ↦ a + (n : ℝ) * (2 * Real.pi / u)) = 1 := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (charFun μ u)).mp hφ
  have hconstOrLt :
      (fun x : ℝ ↦ Complex.exp (u * x * Complex.I)) =ᵐ[μ]
        Function.const ℝ (⨍ x, Complex.exp (u * x * Complex.I) ∂μ) ∨
      ‖∫ x, Complex.exp (u * x * Complex.I) ∂μ‖ < μ.real Set.univ * 1 := by
    refine ae_eq_const_or_norm_integral_lt_of_norm_le_const ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    simpa using le_of_eq (Complex.norm_exp_ofReal_mul_I (u * x))
  -- Equality in the norm bound forces the integrand to have an almost sure constant phase.
  have hphase_ae :
      (fun x : ℝ ↦ Complex.exp (u * x * Complex.I)) =ᵐ[μ]
        Function.const ℝ (Complex.exp (θ * Complex.I)) := by
    rcases hconstOrLt with hconst | hlt
    · filter_upwards [hconst] with x hx
      simpa [average_eq_integral, charFun_apply_real, hθ] using hx
    · have hnorm : ‖∫ x, Complex.exp (u * x * Complex.I) ∂μ‖ = 1 := by
        calc
          ‖∫ x, Complex.exp (u * x * Complex.I) ∂μ‖ = ‖charFun μ u‖ := by
            simp [charFun_apply_real]
          _ = ‖Complex.exp (θ * Complex.I)‖ := by rw [← hθ]
          _ = 1 := Complex.norm_exp_ofReal_mul_I θ
      have hnotlt : ¬ ‖∫ x, Complex.exp (u * x * Complex.I) ∂μ‖ < μ.real Set.univ * 1 := by
        rw [show μ.real Set.univ = 1 by simp, one_mul, hnorm]
        exact lt_irrefl _
      exact False.elim (hnotlt hlt)
  let a : ℝ := θ / u
  let s : Set ℝ := Set.range fun n : ℤ ↦ a + (n : ℝ) * (2 * Real.pi / u)
  have hs_meas : MeasurableSet s := (Set.countable_range _).measurableSet
  have hs_ae : ∀ᵐ x ∂μ, x ∈ s := by
    filter_upwards [hphase_ae] with x hx
    simpa [a, s] using mem_affineIntLattice_of_exp_eq_phase hu hx
  exact ⟨a, (mem_ae_iff_prob_eq_one hs_meas).mp hs_ae⟩

/-- Exercise 15.2.3: a real zero-or-probability law is lattice distributed if and only if there
exists a nonzero
frequency at which the modulus of its characteristic function is equal to `1`. The probability-law
case is the textbook criterion, while the zero measure handles non-measurable pushforwards
canonically. -/
theorem isLatticeDistributed_iff_exists_ne_zero_norm_charFun_eq_one
    (μ : Measure ℝ) [IsZeroOrProbabilityMeasure μ] :
    IsLatticeDistributed μ ↔
      ∃ u : ℝ, u ≠ 0 ∧ ‖charFun μ u‖ = 1 := by
  -- Split the trivial zero-measure case from the genuine probability-law case.
  rcases (eq_zero_or_isProbabilityMeasure (μ := μ)) with rfl | hμ
  · simp [IsLatticeDistributed]
  · letI := hμ
    constructor
    · intro h
      rcases h with ⟨a, d, hμlattice⟩
      by_cases hd : d = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        -- When the lattice collapses to a singleton, frequency `1` already works.
        have hchar : charFun μ 1 = Complex.exp (1 * a * Complex.I) := by
          refine charFun_eq_phase_of_affineIntLattice (μ := μ) (a := a) (d := d) (u := 1)
            hμlattice ?_
          simp [hd]
        calc
          ‖charFun μ 1‖ = ‖Complex.exp (1 * a * Complex.I)‖ := by rw [hchar]
          _ = 1 := by simp
      · refine ⟨2 * Real.pi / d, div_ne_zero (by positivity) hd, ?_⟩
        -- Otherwise choose the frequency whose period is exactly the lattice spacing.
        have hperiod : Complex.exp (((2 * Real.pi / d) * d : ℝ) * Complex.I) = 1 := by
          have hd' : ((2 * Real.pi / d) * d : ℝ) = 2 * Real.pi := by
            field_simp [hd]
          rw [hd']
          simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I 1
        have hchar' := charFun_eq_phase_of_affineIntLattice (μ := μ) (a := a) (d := d)
          (u := 2 * Real.pi / d) hμlattice (by simpa using hperiod)
        have hchar : charFun μ (2 * Real.pi / d) =
            Complex.exp ((2 * Real.pi / d) * a * Complex.I) := by
          simpa using hchar'
        calc
          ‖charFun μ (2 * Real.pi / d)‖ =
              ‖Complex.exp ((2 * Real.pi / d) * a * Complex.I)‖ := by rw [hchar]
          _ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I ((2 * Real.pi / d) * a)
    · rintro ⟨u, hu, hφ⟩
      -- Unit modulus at a nonzero frequency forces affine-lattice support.
      obtain ⟨a, ha⟩ := exists_affineIntLattice_of_norm_charFun_eq_one (μ := μ) hu hφ
      exact ⟨a, 2 * Real.pi / u, ha⟩

end Measure

/-- A real random variable is lattice distributed when its law is lattice distributed. -/
def IsLatticeDistributed (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measure.IsLatticeDistributed (P.map X)

/-- A real random variable is lattice distributed if and only if there exists a
nonzero frequency at which the modulus of its characteristic function is equal to `1`. -/
theorem is_lattice_distributed_iff_exists_ne_zero_norm_charFun_eq_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) :
    IsLatticeDistributed P X ↔
      ∃ u : ℝ, u ≠ 0 ∧ ‖charFun (P.map X) u‖ = 1 := by
  simpa [IsLatticeDistributed] using
    Measure.isLatticeDistributed_iff_exists_ne_zero_norm_charFun_eq_one (P.map X)
