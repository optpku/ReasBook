/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Corollary_9_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Example_11_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

private theorem continuousWithinAt_coe_of_continuousWithinAt_toReal
    {X : Type*} [TopologicalSpace X] {f : X → Set.Ioi (⊥ : EReal)} {x : X}
    (hx : x ∈ effectiveDomain f)
    (hcont : ContinuousWithinAt (fun y : X ↦ (f.asEReal y).toReal) (effectiveDomain f) x) :
    ContinuousWithinAt f.asEReal (effectiveDomain f) x := by
  let g : X → EReal := fun y ↦ (((f.asEReal y).toReal : ℝ) : EReal)
  have hg : ContinuousWithinAt g (effectiveDomain f) x := by
    change Tendsto g (𝓝[effectiveDomain f] x) (𝓝 (g x))
    have hinner :
        Tendsto (fun y : X ↦ (f.asEReal y).toReal) (𝓝[effectiveDomain f] x)
          (𝓝 (f.asEReal x).toReal) := hcont
    have hcoe :
        Tendsto (fun r : ℝ ↦ ((r : ℝ) : EReal)) (𝓝 (f.asEReal x).toReal) (𝓝 (g x)) := by
      simpa [g] using
        (show Tendsto (fun r : ℝ ↦ ((r : ℝ) : EReal)) (𝓝 (f.asEReal x).toReal)
            (𝓝 (((f.asEReal x).toReal : ℝ) : EReal)) from
          continuous_coe_real_ereal.continuousAt.tendsto)
    exact hcoe.comp hinner
  have hEq : g =ᶠ[𝓝[effectiveDomain f] x] f.asEReal := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy_top : f.asEReal y ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : f.asEReal y ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < f.asEReal y from (f y).2)
    simpa [g] using EReal.coe_toReal hy_top hy_bot
  have hxEq : f.asEReal x = g x := by
    have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < f.asEReal x from (f x).2)
    simpa [g] using (EReal.coe_toReal hx_top hx_bot).symm
  exact hg.congr_of_eventuallyEq hEq.symm hxEq

private theorem isMinimizingSequence_of_tendsto_of_mem_argmin_of_continuousWithinAt
    {X : Type*} [TopologicalSpace X] {f : X → Set.Ioi (⊥ : EReal)} {xₙ : ℕ → X} {x : X}
    (hxdom : ∀ n, xₙ n ∈ effectiveDomain f)
    (hcont : ContinuousWithinAt f.asEReal (effectiveDomain f) x)
    (hxmin : x ∈ Argmin f.asEReal)
    (hstrong : Tendsto xₙ atTop (𝓝 x)) :
    IsMinimizingSequence f.asEReal xₙ := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · simpa [dom, effectiveDomain] using hxdom n
  · have hwithin : Tendsto xₙ atTop (𝓝[effectiveDomain f] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hstrong, Filter.Eventually.of_forall hxdom⟩
    have hvalue : Tendsto (fun n ↦ f.asEReal (xₙ n)) atTop (𝓝 (f.asEReal x)) :=
      hcont.tendsto.comp hwithin
    simpa [Function.comp, mem_argmin_iff_eq_sInf.mp hxmin] using hvalue

/-- Remark 11.22 (1): clause (i), real case. For a function in `Γ₀(ℝ)`, any sequence in the
effective domain that converges strongly to a global minimizer is a minimizing sequence. -/
-- Proof sketch: Corollary 9.15 gives continuity of the coerced `EReal`-valued function at the
-- minimizer in the one-dimensional case. Therefore `f (xₙ n) → f x`, and since `x` minimizes `f`,
-- this limit is the infimum of the range.
theorem isMinimizingSequence_of_tendsto_of_mem_argmin_real
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ)) {xₙ : ℕ → ℝ}
    (hxdom : ∀ n, xₙ n ∈ effectiveDomain f) {x : ℝ}
    (hxmin : x ∈ Argmin f.asEReal)
    (hstrong : Tendsto xₙ atTop (𝓝 x)) :
    IsMinimizingSequence f.asEReal xₙ := by
  have hxeff : x ∈ effectiveDomain f :=
    by
      simpa [dom, effectiveDomain] using
        mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hxmin
  have hcont_toReal :
      ContinuousWithinAt (fun y : ℝ ↦ (f.asEReal y).toReal) (effectiveDomain f) x :=
    continuousOn_toReal_effectiveDomain_of_mem_gammaZero hf x hxeff
  exact
    isMinimizingSequence_of_tendsto_of_mem_argmin_of_continuousWithinAt hxdom
      (continuousWithinAt_coe_of_continuousWithinAt_toReal hxeff hcont_toReal) hxmin hstrong

section HilbertSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Remark 11.22 (2): clause (i), interior-domain case. For a function in `Γ₀(H)`, any sequence in
the effective domain that converges strongly to a global minimizer lying in the interior of the
effective domain is a minimizing sequence. -/
-- Proof sketch: Corollary 8.39 yields continuity of the real-valued representative on the
-- interior of the effective domain. At an interior minimizer `x`, this gives `f (xₙ n) → f x`,
-- and the minimizing property of `x` identifies the limit with the infimum of the range.
theorem isMinimizingSequence_of_tendsto_of_mem_argmin_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {xₙ : ℕ → H}
    (hxdom : ∀ n, xₙ n ∈ effectiveDomain f) {x : H}
    (hxmin : x ∈ Argmin f.asEReal)
    (hstrong : Tendsto xₙ atTop (𝓝 x))
    (hxint : x ∈ interior (effectiveDomain f)) :
    IsMinimizingSequence f.asEReal xₙ := by
  have hxeff : x ∈ effectiveDomain f :=
    by
      simpa [dom, effectiveDomain] using
        mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hxmin
  let contPts : Set H :=
    {y | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ effectiveDomain f ∧
      ContinuousAt (fun z : H ↦ (f.asEReal z).toReal) y}
  set_option linter.style.longLine false in
  have hcont_eq :=
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      f hf.2 (Or.inr <| Or.inl hf.1)
  have hcont_pt : x ∈ contPts := by
    change x ∈
        {y | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ effectiveDomain f ∧
          ContinuousAt (fun z : H ↦ (f.asEReal z).toReal) y}
    rw [hcont_eq]
    exact hxint
  rcases hcont_pt with ⟨_, _, _, hcont_toReal⟩
  exact
    isMinimizingSequence_of_tendsto_of_mem_argmin_of_continuousWithinAt hxdom
      (continuousWithinAt_coe_of_continuousWithinAt_toReal hxeff
        hcont_toReal.continuousWithinAt)
      hxmin hstrong

/-- Remark 11.22 (3): clause (ii). Strong convergence to a global minimizer does not force a
minimizing sequence in general; there is already a finite-dimensional counterexample. -/
-- Proof sketch: use the construction cited in Example 9.43, which gives a function in `Γ₀` on a
-- finite-dimensional space together with a sequence in its effective domain converging strongly to
-- a minimizer while the function values fail to converge to the infimum.
theorem exists_strongly_convergent_to_mem_argmin_not_isMinimizingSequence :
    ∃ (f : ℝ × ℝ → Set.Ioi (⊥ : EReal)) (xₙ : ℕ → ℝ × ℝ) (x : ℝ × ℝ),
      f ∈ Γ₀(ℝ × ℝ) ∧
      (∀ n, xₙ n ∈ effectiveDomain f) ∧
      Tendsto xₙ atTop (𝓝 x) ∧
      x ∈ Argmin f.asEReal ∧
      ¬ IsMinimizingSequence f.asEReal xₙ := by
  let ε : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ))) atTop (𝓝 (0 : ℝ)))
  refine ⟨closedScalarRelativeEntropy, example11_25ySequence ε, 0, ?_, ?_, ?_, ?_, ?_⟩
  · exact closedScalarRelativeEntropy_mem_gammaZero
  · intro n
    rw [mem_effectiveDomain_iff]
    have hvalue :
        (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal) =
          ((ε n * Real.log (ε n / Real.exp (-(1 / ε n))) - ε n + Real.exp (-(1 / ε n)) : ℝ) :
            EReal) := by
      simpa [example11_25ySequence] using
        (closedScalarRelativeEntropy_apply_of_pos (hε_pos n) (Real.exp_pos _))
    rw [hvalue]
    exact EReal.coe_lt_top _
  · exact example11_25ySequence_tendsto_zero hε_pos hε_tendsto
  · exact closedScalarRelativeEntropy_origin_mem_argmin
  · intro hmin
    have hzero :
        Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal))
          atTop (𝓝 (0 : EReal)) := by
      simpa [Function.comp, closedScalarRelativeEntropy_sInf_eq_zero] using hmin.tendsto
    have hone :
        Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal))
          atTop (𝓝 (1 : EReal)) :=
      closedScalarRelativeEntropy_value_ySequence_tendsto_one hε_pos hε_tendsto
    have : (0 : EReal) = 1 := tendsto_nhds_unique hzero hone
    norm_num at this

/-- Remark 11.22 (4): clause (iii). Any orthonormal sequence in a real Hilbert space converges
weakly to the interior minimizer `0` of the norm function, but it is not a minimizing sequence for
`x ↦ ‖x‖`. -/
-- Proof sketch: Example 2.32.1 gives weak convergence of every orthonormal sequence to `0`. The
-- norm function has full domain and attains its minimum at `0`, but along an orthonormal sequence
-- all function values are constantly `1`, so they cannot converge to the infimum `0`.
theorem orthonormal_weakly_convergent_to_interior_mem_argmin_not_isMinimizingSequence
    {xₙ : ℕ → H} (hxₙ : Orthonormal ℝ xₙ) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H (0 : H))) ∧
      (0 : H) ∈ interior (dom fun y : H ↦ (‖y‖ : EReal)) ∧
      (0 : H) ∈ Argmin (fun y : H ↦ (‖y‖ : EReal)) ∧
      ¬ IsMinimizingSequence (fun y : H ↦ (‖y‖ : EReal)) xₙ := by
  have hargmin_zero : (0 : H) ∈ Argmin (fun y : H ↦ (‖y‖ : EReal)) := by
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    exact_mod_cast (show ‖(0 : H)‖ ≤ ‖y‖ from by
      rw [norm_zero]
      exact norm_nonneg y)
  refine ⟨orthonormal_sequence_tendsto_zero_weakly xₙ hxₙ, ?_, hargmin_zero, ?_⟩
  · have hdom_norm : dom (fun y : H ↦ (‖y‖ : EReal)) = Set.univ := by
      ext y
      simp [dom]
    rw [hdom_norm]
    simp
  · intro hmin
    have hzero :
        Tendsto (fun n ↦ ((‖xₙ n‖ : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
      have hsInf_zero :
          sInf (Set.range fun y : H ↦ ((‖y‖ : ℝ) : EReal)) = (0 : EReal) := by
        simpa using (mem_argmin_iff_eq_sInf.mp hargmin_zero).symm
      simpa [Function.comp, hsInf_zero] using hmin.tendsto
    have hone :
        Tendsto (fun n ↦ ((‖xₙ n‖ : ℝ) : EReal)) atTop (𝓝 (1 : EReal)) := by
      have hnorm : (fun n ↦ ((‖xₙ n‖ : ℝ) : EReal)) = fun _ : ℕ ↦ (1 : EReal) := by
        ext n
        exact_mod_cast hxₙ.norm_eq_one n
      rw [hnorm]
      exact tendsto_const_nhds
    have : (0 : EReal) = 1 := tendsto_nhds_unique hzero hone
    norm_num at this

/-- Companion bridge for Remark 11.22 (4): in an infinite-dimensional real Hilbert space, the
preceding orthonormal-sequence statement yields an explicit weakly convergent non-minimizing
counterexample for the norm objective. -/
theorem exists_orthonormal_weakly_convergent_to_interior_mem_argmin_not_isMinimizingSequence
    (h_infinite : ¬ FiniteDimensional ℝ H) :
    ∃ xₙ : ℕ → H,
      Orthonormal ℝ xₙ ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H (0 : H))) ∧
      (0 : H) ∈ interior (dom fun y : H ↦ (‖y‖ : EReal)) ∧
      (0 : H) ∈ Argmin (fun y : H ↦ (‖y‖ : EReal)) ∧
      ¬ IsMinimizingSequence (fun y : H ↦ (‖y‖ : EReal)) xₙ := by
  obtain ⟨xₙ, hxₙ⟩ := exists_orthonormal_sequence_of_not_finiteDimensional h_infinite
  exact ⟨xₙ, hxₙ, orthonormal_weakly_convergent_to_interior_mem_argmin_not_isMinimizingSequence hxₙ⟩

end HilbertSpace

end ERealFunction
