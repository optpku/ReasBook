/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Corollary_6_21

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ι : Type v}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Helper for Corollary 6.22: a finite `eVar` bound forces `L²` membership. -/
lemma memLp_two_of_evariance_le {f : Ω → ℝ} (hf_meas : AEStronglyMeasurable f P)
    {C : NNReal} (hC : eVar[f; P] ≤ (C : ENNReal)) : MemLp f 2 P := by
  -- The `NNReal` upper bound puts the extended variance strictly below `∞`.
  refine (ProbabilityTheory.evariance_lt_top_iff_memLp hf_meas).mp ?_
  exact lt_of_le_of_lt hC ENNReal.coe_lt_top

/-- Helper for Corollary 6.22: the second moment is controlled by the square of the mean bound
and the variance bound. -/
lemma integral_sq_le_sq_mean_bound_add_evariance_bound {f : Ω → ℝ}
    (hf_meas : AEStronglyMeasurable f P) {Cm Cv : NNReal}
    (hmean : |P[f]| ≤ (Cm : ℝ)) (hvar : eVar[f; P] ≤ (Cv : ENNReal)) :
    ∫ ω, (f ω) ^ 2 ∂P ≤ (Cm : ℝ) ^ 2 + (Cv : ℝ) := by
  -- Finite variance gives the `L²` hypothesis needed for the variance identity.
  have hLp : MemLp f 2 P := memLp_two_of_evariance_le hf_meas hvar
  have hvar_real : Var[f; P] ≤ (Cv : ℝ) := by
    change (eVar[f; P]).toReal ≤ (Cv : ℝ)
    exact ENNReal.toReal_mono ENNReal.coe_ne_top hvar
  have hmean_left : -((Cm : ℝ)) ≤ P[f] := by
    exact (abs_le.mp hmean).1
  have hmean_right : P[f] ≤ (Cm : ℝ) := by
    exact (abs_le.mp hmean).2
  have hmean_sq : P[f] ^ 2 ≤ (Cm : ℝ) ^ 2 := by
    nlinarith
  have h_second_moment :
      ∫ ω, (f ω) ^ 2 ∂P = Var[f; P] + P[f] ^ 2 := by
    have hvar_eq : Var[f; P] = P[f ^ 2] - P[f] ^ 2 := ProbabilityTheory.variance_eq_sub hLp
    calc
      ∫ ω, (f ω) ^ 2 ∂P = P[f ^ 2] := by rfl
      _ = Var[f; P] + P[f] ^ 2 := by linarith
  -- Rewrite `E[f²]` as `Var[f] + E[f]²` and estimate both summands.
  calc
    ∫ ω, (f ω) ^ 2 ∂P = Var[f; P] + P[f] ^ 2 := h_second_moment
    _ ≤ (Cv : ℝ) + (Cm : ℝ) ^ 2 := by
      nlinarith
    _ = (Cm : ℝ) ^ 2 + (Cv : ℝ) := by ring

/-- Helper for Corollary 6.22: a bounded second moment gives a uniform `L²` seminorm bound. -/
lemma eLpNorm_two_le_of_integral_sq_le (μ : Measure Ω) {f : Ω → ℝ} (hf_memLp : MemLp f 2 μ)
    {M : ℝ} (hM : ∫ ω, (f ω) ^ 2 ∂μ ≤ M) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt M) := by
  have h_sq_nonneg : 0 ≤ ∫ ω, (f ω) ^ 2 ∂μ := by
    exact integral_nonneg fun _ ↦ sq_nonneg _
  calc
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ)) := by
      simpa [Real.sqrt_eq_rpow, one_div, sq_abs] using
        (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hf_memLp)
    _ ≤ ENNReal.ofReal (Real.sqrt M) := by
      exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hM)

-- Proof sketch: the `NNReal` bound on `eVar` and measurability give a uniform `L²` bound after
-- rewriting the second moment as the sum of the variance and the square of the expectation on a
-- probability space. Then apply Corollary 6.21 with exponent `p = 2`.
/-- Corollary 6.22: if a family of real random variables on a probability space has uniformly
bounded absolute expectations and uniformly bounded finite variances, then it is uniformly
integrable. The bounds are stated with `NNReal` constants; in particular, the variance bound is an
`NNReal` upper bound on `eVar`, so finiteness is part of the Lean statement. -/
theorem uniformIntegrable_of_bounded_expectation_and_evariance
    {X : ι → Ω → ℝ} (hX_meas : ∀ i, AEStronglyMeasurable (X i) P)
    (h_mean_bdd : ∃ C : NNReal, ∀ i, |P[X i]| ≤ (C : ℝ))
    (h_evar_bdd : ∃ C : NNReal, ∀ i, eVar[X i; P] ≤ (C : ENNReal)) :
    UniformIntegrable X 1 P := by
  obtain ⟨Cm, hCm⟩ := h_mean_bdd
  obtain ⟨Cv, hCv⟩ := h_evar_bdd
  let M : ℝ := (Cm : ℝ) ^ 2 + (Cv : ℝ)
  have hM : 0 ≤ M := by
    positivity
  let C : NNReal := ⟨Real.sqrt M, Real.sqrt_nonneg _⟩
  let Y : ι → Lp ℝ (ENNReal.ofReal (2 : ℝ)) P := fun i ↦
    let hLp_i : MemLp (X i) (ENNReal.ofReal (2 : ℝ)) P := by
      simpa using memLp_two_of_evariance_le (hX_meas i) (hCv i)
    hLp_i.toLp (X i)
  let F : Set (Lp ℝ (ENNReal.ofReal (2 : ℝ)) P) := Set.range Y
  have hone_le_two : (1 : ENNReal) ≤ ENNReal.ofReal (2 : ℝ) := by
    norm_num
  have hF_bdd : by
      letI := Fact.mk hone_le_two
      exact Bornology.IsBounded F := by
    letI := Fact.mk hone_le_two
    refine isBounded_iff_forall_norm_le.2 ⟨(C : ℝ), ?_⟩
    intro f hf
    rcases hf with ⟨i, rfl⟩
    have hLp_i_two : MemLp (X i) 2 P := memLp_two_of_evariance_le (hX_meas i) (hCv i)
    have hLp_i : MemLp (X i) (ENNReal.ofReal (2 : ℝ)) P := by
      simpa using hLp_i_two
    have h_sq_i : ∫ ω, (X i ω) ^ 2 ∂P ≤ M := by
      simpa [M] using
        integral_sq_le_sq_mean_bound_add_evariance_bound (hX_meas i) (hCm i) (hCv i)
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top <| by
      calc
        eLpNorm (X i) (ENNReal.ofReal (2 : ℝ)) P = eLpNorm (X i) 2 P := by
          simp
        _ ≤ ENNReal.ofReal (Real.sqrt M) := eLpNorm_two_le_of_integral_sq_le P hLp_i_two h_sq_i
        _ = (C : ENNReal) := by
          simpa [C] using ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg M)
  have hUI_F : UniformIntegrable ((↑) : F → Ω → ℝ) 1 P :=
    uniformIntegrable_of_bounded_memLp_of_one_lt (p := 2) (F := F) P
      (show 1 < (2 : ℝ) by norm_num) hF_bdd
  let Ysub : ι → F := fun i ↦ ⟨Y i, ⟨i, rfl⟩⟩
  have hUI_Y : UniformIntegrable (fun i ↦ ((Ysub i : F) : Ω → ℝ)) 1 P := by
    refine ⟨fun i ↦ hUI_F.1 (Ysub i), ?_, ?_⟩
    · intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := hUI_F.2.1 hε
      exact ⟨δ, hδpos, fun i s hs hμs ↦ hδ (Ysub i) s hs hμs⟩
    · obtain ⟨B, hB⟩ := hUI_F.2.2
      exact ⟨B, fun i ↦ hB (Ysub i)⟩
  refine hUI_Y.ae_eq ?_
  intro i
  simpa [Ysub, Y] using
    (MemLp.coeFn_toLp (by
      simpa using memLp_two_of_evariance_le (hX_meas i) (hCv i)) : (Y i : Ω → ℝ) =ᵐ[P] X i)
