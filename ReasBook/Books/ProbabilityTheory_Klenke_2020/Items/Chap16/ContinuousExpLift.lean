/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped Topology

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- A continuous zero-free complex-valued function on `ℝ` normalized by `φ 0 = 1` admits a
unique continuous lift through `Complex.exp` starting at `0`. -/
lemma existsUniqueContinuousExpLift {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφne : ∀ x : ℝ, φ x ≠ 0) (hφ0 : φ 0 = 1) :
    ∃! Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ t) = φ t := by
  let f : C(ℝ, {z : ℂ // z ≠ 0}) :=
    ⟨fun t ↦ ⟨φ t, hφne t⟩, hφc.subtype_mk _⟩
  have he :
      (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 = f 0 := by
    ext
    simp [f, hφ0]
  rcases Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 he with
    ⟨Ψ, hΨ, hΨuniq⟩
  refine ⟨Ψ, ?_, ?_⟩
  · rcases hΨ with ⟨hΨ0, hΨexp⟩
    refine ⟨hΨ0, ?_⟩
    intro t
    simpa [f] using congrArg Subtype.val (congr_fun hΨexp t)
  · intro Ψ' hΨ'
    apply hΨuniq
    rcases hΨ' with ⟨hΨ'0, hΨ'exp⟩
    refine ⟨hΨ'0, ?_⟩
    funext t
    change (⟨Complex.exp (Ψ' t), (Ψ' t).exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) = f t
    apply Subtype.ext
    simpa [f] using hΨ'exp t

end MeasureTheory.ProbabilityMeasure
