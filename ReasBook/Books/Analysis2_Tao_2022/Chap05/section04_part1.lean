/-
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap05.section03

section Chap05
section Section04

/-- Helper for Theorem 5.4.1: extract a Fourier-span element that approximates a target
continuous function within a prescribed sup-norm error. -/
lemma helperForTheorem_5_4_1_dense_span_witness
    (f : C(AddCircle (1 : ℝ), ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : C(AddCircle (1 : ℝ), ℂ),
      P ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ∧ ‖f - P‖ < ε := by
  have hf_mem_submodule_closure :
      f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  have hf_mem_set_closure :
      f ∈ closure
        (↑(Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ) :
          Set (C(AddCircle (1 : ℝ), ℂ))) := by
    simpa [Submodule.topologicalClosure_coe] using hf_mem_submodule_closure
  rcases Metric.mem_closure_iff.mp hf_mem_set_closure ε hε with ⟨P, hPspan, hdist⟩
  refine ⟨P, hPspan, ?_⟩
  simpa [dist_eq_norm] using hdist

/-- Helper for Theorem 5.4.1: every element of the Fourier span has a finite
`Finsupp` expansion in the characters `fourierCharacter n`. -/
lemma helperForTheorem_5_4_1_span_element_has_finsupp_expansion
    {P : C(AddCircle (1 : ℝ), ℂ)}
    (hP : P ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) :
    ∃ c : ℤ →₀ ℂ, P = c.sum (fun n a => a • fourierCharacter n) := by
  rcases (Finsupp.mem_span_range_iff_exists_finsupp.mp hP) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  simpa [fourierCharacter] using hc.symm

/-- Helper for Theorem 5.4.1: the support of a finitely supported coefficient family
is contained in a symmetric interval `[-N, N]`, with
`N = c.support.sup Int.natAbs`. -/
lemma helperForTheorem_5_4_1_support_in_symmetric_Icc
    (c : ℤ →₀ ℂ) :
    let N : ℕ := c.support.sup Int.natAbs
    ∀ n ∈ c.support, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  intro N n hn
  have hn_le_N_nat : Int.natAbs n ≤ N := by
    have hs : Int.natAbs n ≤ c.support.sup Int.natAbs := Finset.le_sup hn
    simpa [N] using hs
  have hAbs_le : |n| ≤ (N : ℤ) := by
    have hcast : (Int.natAbs n : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast hn_le_N_nat
    calc
      |n| = (Int.natAbs n : ℤ) := Int.abs_eq_natAbs n
      _ ≤ (N : ℤ) := hcast
  have hBounds : (-(N : ℤ)) ≤ n ∧ n ≤ (N : ℤ) := (abs_le.mp hAbs_le)
  simpa [Finset.mem_Icc] using hBounds

/-- Helper for Theorem 5.4.1: every finite Fourier-character expansion is a
trigonometric polynomial in the sense of Definition 5.3.2. -/
lemma helperForTheorem_5_4_1_isTrig_of_finsupp_expansion
    (c : ℤ →₀ ℂ) :
    IsTrigonometricPolynomial (c.sum (fun n a => a • fourierCharacter n)) := by
  classical
  let N : ℕ := c.support.sup Int.natAbs
  let d : ℤ → ℂ := fun n => if n ∈ c.support then c n else 0
  refine ⟨N, d, ?_⟩
  have hsupport_subset : c.support ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n hn
    have hs := helperForTheorem_5_4_1_support_in_symmetric_Icc c
    simpa [N] using hs n hn
  have hsum_support_eq_Icc :
      (∑ n ∈ c.support, d n • fourierCharacter n) =
        (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), d n • fourierCharacter n) := by
    refine Finset.sum_subset hsupport_subset ?_
    intro n hnIcc hnNotMem
    by_cases hcn : c n = 0
    · have hz : d n = 0 := by
        simp [d, hcn]
      rw [hz]
      exact zero_smul ℂ (fourierCharacter n)
    · exfalso
      exact hnNotMem (Finsupp.mem_support_iff.mpr hcn)
  have hsum_finsupp_eq_support :
      c.sum (fun n a => a • fourierCharacter n) =
        (∑ n ∈ c.support, d n • fourierCharacter n) := by
    calc
      c.sum (fun n a => a • fourierCharacter n)
          = ∑ n ∈ c.support, c n • fourierCharacter n := by
              simp [Finsupp.sum]
      _ = ∑ n ∈ c.support, d n • fourierCharacter n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hcn : c n = 0
            · have hnnot : n ∉ c.support := Finsupp.notMem_support_iff.mpr hcn
              exact (hnnot hn).elim
            · simp [d, hcn]
  calc
    c.sum (fun n a => a • fourierCharacter n)
        = ∑ n ∈ c.support, d n • fourierCharacter n := hsum_finsupp_eq_support
    _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), d n • fourierCharacter n := hsum_support_eq_Icc

/-- Theorem 5.4.1 (Weierstrass approximation theorem for trigonometric polynomials):
for every continuous function `f : C(ℝ/ℤ; ℂ)` and every `ε > 0`, there exists a
trigonometric polynomial `P` such that `‖f - P‖ ≤ ε`. -/
theorem exists_trigonometricPolynomial_uniform_approximation
    (f : C(AddCircle (1 : ℝ), ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : C(AddCircle (1 : ℝ), ℂ),
      IsTrigonometricPolynomial P ∧ ‖f - P‖ ≤ ε := by
  rcases helperForTheorem_5_4_1_dense_span_witness f ε hε with ⟨P, hPspan, hPdist⟩
  rcases helperForTheorem_5_4_1_span_element_has_finsupp_expansion hPspan with ⟨c, rfl⟩
  refine ⟨c.sum (fun n a => a • fourierCharacter n),
    helperForTheorem_5_4_1_isTrig_of_finsupp_expansion c, ?_⟩
  exact le_of_lt hPdist

/-- Continuity of the function underlying periodic convolution. -/
lemma periodicConvolution_continuous
    (f g : C(AddCircle (1 : ℝ), ℂ)) :
    Continuous (fun x : AddCircle (1 : ℝ) =>
      ∫ y in Set.Icc (0 : ℝ) 1, f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ)))) := by
  have hHasCompactSupport :
      HasCompactSupport (fun t : AddCircle (1 : ℝ) => g t) := by
    refine HasCompactSupport.intro isCompact_univ ?_
    intro x hx
    exact (hx (Set.mem_univ x)).elim
  have hConvolutionContinuous :
      Continuous
        (MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
          (fun t : AddCircle (1 : ℝ) => g t)
          (ContinuousLinearMap.mul ℂ ℂ)
          (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))) := by
    simpa using
      (hHasCompactSupport.continuous_convolution_right
        (L := (ContinuousLinearMap.mul ℂ ℂ))
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))
        (hf := f.continuous.locallyIntegrable)
        (hg := g.continuous))
  have hRewrite :
      (fun x : AddCircle (1 : ℝ) =>
        ∫ y in Set.Icc (0 : ℝ) 1,
          f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ))))
        =
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    funext x
    calc
      (∫ y in Set.Icc (0 : ℝ) 1,
          f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ))))
          = ∫ y in Set.Ioc (0 : ℝ) 1,
              f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ))) := by
                rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = ∫ t : AddCircle (1 : ℝ), f t * g (x - t) := by
            simpa using (AddCircle.integral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
              (f := fun z : AddCircle (1 : ℝ) => f z * g (x - z)))
      _ = MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
            (fun t : AddCircle (1 : ℝ) => g t)
            (ContinuousLinearMap.mul ℂ ℂ)
            (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) x := by
            rw [MeasureTheory.convolution_def]
            simp
  simpa [hRewrite] using hConvolutionContinuous

/-- Definition 5.4.2: for continuous `f, g : C(ℝ/ℤ; ℂ)`, the periodic convolution
is the continuous function on `ℝ/ℤ` given by
`(f * g)(x) = ∫ y ∈ [0,1], f(y) g(x - y) dy` with `y` viewed in `ℝ/ℤ`. -/
noncomputable def periodicConvolution (f g : C(AddCircle (1 : ℝ), ℂ)) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨(fun x : AddCircle (1 : ℝ) =>
      ∫ y in Set.Icc (0 : ℝ) 1, f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ)))),
    periodicConvolution_continuous f g⟩

/-- Lemma 5.4.4a (Basic properties of periodic convolution (a), Closure):
if `f, g ∈ C(ℝ/ℤ; ℂ)`, then `f * g ∈ C(ℝ/ℤ; ℂ)`.
In this file, `f * g` is represented by `periodicConvolution f g`. -/
lemma periodicConvolution_continuous_closure
    (f g : C(AddCircle (1 : ℝ), ℂ)) :
    Continuous (periodicConvolution f g) := by
  exact (periodicConvolution f g).continuous

/-- Helper for Lemma 5.4.4b: rewrite the periodic-convolution integral on `Set.Icc`
as an evaluation of convolution on `AddCircle (1 : ℝ)`. -/
lemma helperForLemma_5_4_4b_eval_eq_addcircle_convolution
    (f g : C(AddCircle (1 : ℝ), ℂ)) (x : AddCircle (1 : ℝ)) :
    (∫ y in Set.Icc (0 : ℝ) 1, f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ)))) =
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) x := by
  calc
    (∫ y in Set.Icc (0 : ℝ) 1, f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ))))
        = ∫ y in Set.Ioc (0 : ℝ) 1, f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ))) := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ t : AddCircle (1 : ℝ), f t * g (x - t) := by
          simpa using (AddCircle.integral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
            (f := fun z : AddCircle (1 : ℝ) => f z * g (x - z)))
    _ = MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
          (fun t : AddCircle (1 : ℝ) => g t)
          (ContinuousLinearMap.mul ℂ ℂ)
          (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) x := by
          rw [MeasureTheory.convolution_def]
          simp

/-- Helper for Lemma 5.4.4b: for complex-valued convolution, replacing `mul` by
`mul.flip` does not change the result. -/
lemma helperForLemma_5_4_4b_mul_convolution_eq_flip_convolution
    (F G : AddCircle (1 : ℝ) → ℂ) :
    MeasureTheory.convolution G F (ContinuousLinearMap.mul ℂ ℂ)
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
    MeasureTheory.convolution G F (ContinuousLinearMap.mul ℂ ℂ).flip
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
  ext x
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  simp

/-- Helper for Lemma 5.4.4b: convolution on `AddCircle (1 : ℝ)` with complex
multiplication is commutative. -/
lemma helperForLemma_5_4_4b_addcircle_convolution_comm
    (F G : AddCircle (1 : ℝ) → ℂ) :
    MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ)
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
    MeasureTheory.convolution G F (ContinuousLinearMap.mul ℂ ℂ)
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
  calc
    MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ)
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))
        = MeasureTheory.convolution G F (ContinuousLinearMap.mul ℂ ℂ).flip
            (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
              simpa using (MeasureTheory.convolution_flip
                (L := (ContinuousLinearMap.mul ℂ ℂ))
                (f := F) (g := G)
                (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))).symm
    _ = MeasureTheory.convolution G F (ContinuousLinearMap.mul ℂ ℂ)
          (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
            exact (helperForLemma_5_4_4b_mul_convolution_eq_flip_convolution F G).symm

/-- Lemma 5.4.4b (Basic properties of periodic convolution (b), Commutativity):
for `f, g : C(ℝ/ℤ; ℂ)`, one has `f * g = g * f`, represented here as
`periodicConvolution f g = periodicConvolution g f`. -/
lemma periodicConvolution_comm
    (f g : C(AddCircle (1 : ℝ), ℂ)) :
    periodicConvolution f g = periodicConvolution g f := by
  ext x
  change (∫ y in Set.Icc (0 : ℝ) 1,
      f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ)))) =
    (∫ y in Set.Icc (0 : ℝ) 1,
      g (y : AddCircle (1 : ℝ)) * f (x - (y : AddCircle (1 : ℝ))))
  rw [helperForLemma_5_4_4b_eval_eq_addcircle_convolution,
    helperForLemma_5_4_4b_eval_eq_addcircle_convolution]
  exact congrArg (fun h : AddCircle (1 : ℝ) → ℂ => h x)
    (helperForLemma_5_4_4b_addcircle_convolution_comm
      (fun t : AddCircle (1 : ℝ) => f t)
      (fun t : AddCircle (1 : ℝ) => g t))

/-- Lemma 5.4.4c (Basic properties of periodic convolution (c), Bilinearity):
for `f, g, h : C(ℝ/ℤ; ℂ)` and `c : ℂ`, one has
`f * (g + h) = f * g + f * h`, `(f + g) * h = f * h + g * h`, and
`c (f * g) = (c f) * g = f * (c g)`, represented here using `periodicConvolution`. -/
lemma periodicConvolution_bilinearity
    (f g h : C(AddCircle (1 : ℝ), ℂ)) (c : ℂ) :
    periodicConvolution f (g + h) = periodicConvolution f g + periodicConvolution f h ∧
    periodicConvolution (f + g) h = periodicConvolution f h + periodicConvolution g h ∧
    c • periodicConvolution f g = periodicConvolution (c • f) g ∧
    periodicConvolution (c • f) g = periodicConvolution f (c • g) := by
  have hHasCompactSupport :
      ∀ F : AddCircle (1 : ℝ) → ℂ, HasCompactSupport F := by
    intro F
    refine HasCompactSupport.intro isCompact_univ ?_
    intro x hx
    exact (hx (Set.mem_univ x)).elim
  have hConv_f_g :
      MeasureTheory.ConvolutionExists (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    refine (hHasCompactSupport (fun t : AddCircle (1 : ℝ) => g t)).convolutionExists_right
      (L := (ContinuousLinearMap.mul ℂ ℂ)) ?_ ?_
    · exact f.continuous.locallyIntegrable
    · exact g.continuous
  have hConv_f_h :
      MeasureTheory.ConvolutionExists (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => h t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    refine (hHasCompactSupport (fun t : AddCircle (1 : ℝ) => h t)).convolutionExists_right
      (L := (ContinuousLinearMap.mul ℂ ℂ)) ?_ ?_
    · exact f.continuous.locallyIntegrable
    · exact h.continuous
  have hConv_g_h :
      MeasureTheory.ConvolutionExists (fun t : AddCircle (1 : ℝ) => g t)
        (fun t : AddCircle (1 : ℝ) => h t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    refine (hHasCompactSupport (fun t : AddCircle (1 : ℝ) => h t)).convolutionExists_right
      (L := (ContinuousLinearMap.mul ℂ ℂ)) ?_ ?_
    · exact g.continuous.locallyIntegrable
    · exact h.continuous
  have hConvolution_distrib_add_right :
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => (g + h) t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) +
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => h t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    simpa [Pi.add_apply] using
      (MeasureTheory.ConvolutionExists.distrib_add
        (L := (ContinuousLinearMap.mul ℂ ℂ))
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))
        hConv_f_g hConv_f_h)
  have hConvolution_distrib_add_left :
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => (f + g) t)
        (fun t : AddCircle (1 : ℝ) => h t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => h t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) +
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => g t)
        (fun t : AddCircle (1 : ℝ) => h t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    simpa [Pi.add_apply] using
      (MeasureTheory.ConvolutionExists.add_distrib
        (L := (ContinuousLinearMap.mul ℂ ℂ))
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))
        hConv_f_h hConv_g_h)
  have hConvolution_smul_left :
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => (c • f) t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
      c • MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    simpa [Pi.smul_apply] using
      (MeasureTheory.smul_convolution
        (L := (ContinuousLinearMap.mul ℂ ℂ))
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))
        (f := (fun t : AddCircle (1 : ℝ) => f t))
        (g := (fun t : AddCircle (1 : ℝ) => g t))
        (y := c))
  have hConvolution_smul_right :
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => (c • g) t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
      c • MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    simpa [Pi.smul_apply] using
      (MeasureTheory.convolution_smul
        (L := (ContinuousLinearMap.mul ℂ ℂ))
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))
        (f := (fun t : AddCircle (1 : ℝ) => f t))
        (g := (fun t : AddCircle (1 : ℝ) => g t))
        (y := c))
  have hConvolution_smul_bridge :
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => (c • f) t)
        (fun t : AddCircle (1 : ℝ) => g t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
        (fun t : AddCircle (1 : ℝ) => (c • g) t)
        (ContinuousLinearMap.mul ℂ ℂ)
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    calc
      MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => (c • f) t)
          (fun t : AddCircle (1 : ℝ) => g t)
          (ContinuousLinearMap.mul ℂ ℂ)
          (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))
          = c • MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
              (fun t : AddCircle (1 : ℝ) => g t)
              (ContinuousLinearMap.mul ℂ ℂ)
              (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) :=
            hConvolution_smul_left
      _ = MeasureTheory.convolution (fun t : AddCircle (1 : ℝ) => f t)
            (fun t : AddCircle (1 : ℝ) => (c • g) t)
            (ContinuousLinearMap.mul ℂ ℂ)
            (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) :=
          hConvolution_smul_right.symm
  constructor
  · ext x
    change (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * (g + h) (x - (y : AddCircle (1 : ℝ)))) =
      (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ)))) +
      (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * h (x - (y : AddCircle (1 : ℝ))))
    rw [helperForLemma_5_4_4b_eval_eq_addcircle_convolution,
      helperForLemma_5_4_4b_eval_eq_addcircle_convolution,
      helperForLemma_5_4_4b_eval_eq_addcircle_convolution]
    exact congrArg (fun k : AddCircle (1 : ℝ) → ℂ => k x) hConvolution_distrib_add_right
  constructor
  · ext x
    change (∫ y in Set.Icc (0 : ℝ) 1,
        (f + g) (y : AddCircle (1 : ℝ)) * h (x - (y : AddCircle (1 : ℝ)))) =
      (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * h (x - (y : AddCircle (1 : ℝ)))) +
      (∫ y in Set.Icc (0 : ℝ) 1,
        g (y : AddCircle (1 : ℝ)) * h (x - (y : AddCircle (1 : ℝ))))
    rw [helperForLemma_5_4_4b_eval_eq_addcircle_convolution,
      helperForLemma_5_4_4b_eval_eq_addcircle_convolution,
      helperForLemma_5_4_4b_eval_eq_addcircle_convolution]
    exact congrArg (fun k : AddCircle (1 : ℝ) → ℂ => k x) hConvolution_distrib_add_left
  constructor
  · ext x
    change c • (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ)))) =
      (∫ y in Set.Icc (0 : ℝ) 1,
        (c • f) (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ))))
    rw [helperForLemma_5_4_4b_eval_eq_addcircle_convolution,
      helperForLemma_5_4_4b_eval_eq_addcircle_convolution]
    exact congrArg (fun k : AddCircle (1 : ℝ) → ℂ => k x) hConvolution_smul_left.symm
  · ext x
    change (∫ y in Set.Icc (0 : ℝ) 1,
        (c • f) (y : AddCircle (1 : ℝ)) * g (x - (y : AddCircle (1 : ℝ)))) =
      (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * (c • g) (x - (y : AddCircle (1 : ℝ)))
      )
    rw [helperForLemma_5_4_4b_eval_eq_addcircle_convolution,
      helperForLemma_5_4_4b_eval_eq_addcircle_convolution]
    exact congrArg (fun k : AddCircle (1 : ℝ) → ℂ => k x) hConvolution_smul_bridge

/-- Helper for Lemma 5.4.5: factor a character at a difference into a product of
an `x`-factor and a `y`-factor. -/
lemma helperForLemma_5_4_5_character_sub_factorization
    (n : ℤ) (x y : AddCircle (1 : ℝ)) :
    fourierCharacter n (x - y) = fourierCharacter n x * fourierCharacter (-n) y := by
  simp [fourierCharacter, fourier_apply, sub_eq_add_neg, zsmul_add, neg_zsmul,
    AddCircle.toCircle_add]

/-- Helper for Lemma 5.4.5: identify the interval integral appearing in the
character-convolution computation with the Fourier coefficient. -/
lemma helperForLemma_5_4_5_intervalIntegral_eq_fourierTransform
    (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℤ) :
    (∫ y in Set.Icc (0 : ℝ) 1,
      f (y : AddCircle (1 : ℝ)) * fourierCharacter (-n) (y : AddCircle (1 : ℝ)))
      = fourierTransform f n := by
  calc
    (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * fourierCharacter (-n) (y : AddCircle (1 : ℝ)))
        = ∫ y in Set.Ioc (0 : ℝ) 1,
            f (y : AddCircle (1 : ℝ)) * fourierCharacter (-n) (y : AddCircle (1 : ℝ)) := by
            rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ y : AddCircle (1 : ℝ), f y * fourierCharacter (-n) y := by
          simpa using (AddCircle.integral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
            (f := fun z : AddCircle (1 : ℝ) => f z * fourierCharacter (-n) z))
    _ = ∫ y : AddCircle (1 : ℝ), fourierCharacter (-n) y • f y := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          simp [smul_eq_mul, mul_comm]
    _ = fourierTransform f n := by
          simp [fourierTransform, fourierCharacter, fourierCoeff,
            AddCircle.volume_eq_smul_haarAddCircle]

/-- Helper for Lemma 5.4.5: periodic convolution is scalar-linear in the
second argument. -/
lemma helperForLemma_5_4_5_convolution_right_smul
    (f g : C(AddCircle (1 : ℝ), ℂ)) (c : ℂ) :
    periodicConvolution f (c • g) = c • periodicConvolution f g := by
  have hBilinear := periodicConvolution_bilinearity f g g c
  have hLeftSmul : c • periodicConvolution f g = periodicConvolution (c • f) g :=
    hBilinear.2.2.1
  have hBridge : periodicConvolution (c • f) g = periodicConvolution f (c • g) :=
    hBilinear.2.2.2
  calc
    periodicConvolution f (c • g)
        = periodicConvolution (c • f) g := hBridge.symm
    _ = c • periodicConvolution f g := hLeftSmul.symm

/-- Helper for Lemma 5.4.5: each Fourier character is an eigenfunction of
periodic convolution with eigenvalue equal to the corresponding Fourier
coefficient of the left factor. -/
lemma helperForLemma_5_4_5_convolution_with_character
    (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℤ) :
    periodicConvolution f (fourierCharacter n) = (fourierTransform f n) • fourierCharacter n := by
  ext x
  change (∫ y in Set.Icc (0 : ℝ) 1,
      f (y : AddCircle (1 : ℝ)) * fourierCharacter n (x - (y : AddCircle (1 : ℝ))))
    = ((fourierTransform f n) • fourierCharacter n) x
  simp only [ContinuousMap.smul_apply]
  calc
    (∫ y in Set.Icc (0 : ℝ) 1,
        f (y : AddCircle (1 : ℝ)) * fourierCharacter n (x - (y : AddCircle (1 : ℝ))))
      = ∫ y in Set.Icc (0 : ℝ) 1,
          fourierCharacter n x *
            (f (y : AddCircle (1 : ℝ)) * fourierCharacter (-n) (y : AddCircle (1 : ℝ))) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with y
            rw [helperForLemma_5_4_5_character_sub_factorization n x (y : AddCircle (1 : ℝ))]
            ring
    _ = fourierCharacter n x *
          (∫ y in Set.Icc (0 : ℝ) 1,
            f (y : AddCircle (1 : ℝ)) * fourierCharacter (-n) (y : AddCircle (1 : ℝ))) := by
            rw [MeasureTheory.integral_const_mul]
    _ = fourierCharacter n x * (fourierTransform f n) := by
          rw [helperForLemma_5_4_5_intervalIntegral_eq_fourierTransform f n]
    _ = fourierTransform f n * fourierCharacter n x := by
          ring

/-- Helper for Lemma 5.4.5: convolution with a trigonometric polynomial acts
termwise on its Fourier expansion. -/
lemma helperForLemma_5_4_5_convolution_finite_fourier_sum
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) (c : ℤ → ℂ) :
    periodicConvolution f
      (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k => c k • fourierCharacter k))
      =
    Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun k => (fourierTransform f k * c k) • fourierCharacter k) := by
  classical
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  change periodicConvolution f (Finset.sum s (fun k => c k • fourierCharacter k)) =
    Finset.sum s (fun k => (fourierTransform f k * c k) • fourierCharacter k)
  refine Finset.induction_on s ?_ ?_
  · ext x
    simp [periodicConvolution]
  · intro a t ha ht
    have hAdd := (periodicConvolution_bilinearity f (c a • fourierCharacter a)
      (Finset.sum t (fun k => c k • fourierCharacter k)) (1 : ℂ)).1
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hAdd, ht]
    have hHead :
        periodicConvolution f (c a • fourierCharacter a) =
          (fourierTransform f a * c a) • fourierCharacter a := by
      calc
      periodicConvolution f (c a • fourierCharacter a)
          = c a • periodicConvolution f (fourierCharacter a) :=
              helperForLemma_5_4_5_convolution_right_smul f (fourierCharacter a) (c a)
      _ = c a • ((fourierTransform f a) • fourierCharacter a) := by
            rw [helperForLemma_5_4_5_convolution_with_character f a]
      _ = (fourierTransform f a * c a) • fourierCharacter a := by
            simp [smul_smul, mul_comm]
    exact congrArg (fun u => u + Finset.sum t (fun k => (fourierTransform f k * c k) • fourierCharacter k))
      hHead

/-- Lemma 5.4.5: for `f ∈ C(ℝ/ℤ; ℂ)` and `n ∈ ℤ`, one has
`f * e_n = \hat f(n)e_n`. More generally, for a trigonometric polynomial
`P = ∑_{k=-N}^{N} c_k e_k`, periodic convolution acts termwise:
`f * P = ∑_{k=-N}^{N} \hat f(k)c_k e_k`, hence `f * P` is trigonometric. -/
lemma periodicConvolution_fourierCharacter_and_trigSum
    (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    periodicConvolution f (fourierCharacter n) = (fourierTransform f n) • fourierCharacter n ∧
    periodicConvolution f
      (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k => c k • fourierCharacter k))
      =
    Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun k => (fourierTransform f k * c k) • fourierCharacter k) ∧
    IsTrigonometricPolynomial
      (periodicConvolution f
        (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k => c k • fourierCharacter k))) := by
  constructor
  · exact helperForLemma_5_4_5_convolution_with_character f n
  constructor
  · exact helperForLemma_5_4_5_convolution_finite_fourier_sum f N c
  · refine ⟨N, fun k => fourierTransform f k * c k, ?_⟩
    exact helperForLemma_5_4_5_convolution_finite_fourier_sum f N c

/-- Definition 5.4.5 (Periodic approximation to the identity): for `ε > 0` and
`0 < δ < 1/2`, a continuous periodic function `f : C(ℝ/ℤ; ℂ)` is a periodic
`(ε, δ)` approximation to the identity iff
(a) `f(x)` is real and nonnegative for all `x`, and `∫_[0,1] f = 1`, and
(b) `|f(x)| < ε` whenever `δ ≤ |x| ≤ 1 - δ`. -/
def IsPeriodicApproximationToIdentity
    (ε δ : ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) : Prop :=
  0 < ε ∧
  0 < δ ∧
  δ < (1 / 2 : ℝ) ∧
  (∀ x : AddCircle (1 : ℝ), (f x).im = 0 ∧ 0 ≤ (f x).re) ∧
  (∫ y in Set.Icc (0 : ℝ) 1, f (y : AddCircle (1 : ℝ))) = (1 : ℂ) ∧
  ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 - δ → ‖f (x : AddCircle (1 : ℝ))‖ < ε


end Section04
end Chap05
