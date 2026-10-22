/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Set

universe u v

section

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {κ : Ω₁ → Measure Ω₂}
variable {E : Set (Set Ω₂)}

private theorem measurable_measure_univ_of_exhaustion
    (hκ : ∀ A ∈ E, Measurable fun ω₁ ↦ κ ω₁ A)
    {En : ℕ → Set Ω₂} (hEn_mono : Monotone En) (hEn_mem : ∀ n, En n ∈ E)
    (hEn_spanning : (⋃ n, En n) = univ) :
    Measurable fun ω₁ ↦ κ ω₁ univ := by
  have hEn_meas : ∀ n, Measurable fun ω₁ ↦ κ ω₁ (En n) := fun n ↦ hκ (En n) (hEn_mem n)
  have h_iSup : Measurable fun ω₁ ↦ ⨆ n, κ ω₁ (En n) := Measurable.iSup hEn_meas
  have h_eq : (fun ω₁ ↦ κ ω₁ univ) = fun ω₁ ↦ ⨆ n, κ ω₁ (En n) := by
    funext ω₁
    have h_union : κ ω₁ (⋃ n, En n) = ⨆ n, κ ω₁ (En n) := hEn_mono.measure_iUnion
    simpa [hEn_spanning] using h_union
  rw [h_eq]
  exact h_iSup

/-- Remark 8.26: to verify the measurability clause in Definition 8.25 for a finite-measure family
`κ`, it is enough to check the section maps `ω₁ ↦ κ ω₁ A` on a generating `π`-system `E`
containing `Ω₂`. -/
theorem _root_.Measurable.measure_of_isPiSystem_of_univ_mem
    [∀ ω₁, IsFiniteMeasure (κ ω₁)]
    (hgen : ‹MeasurableSpace Ω₂› = MeasurableSpace.generateFrom E) (hE_pi : IsPiSystem E)
    (hκ : ∀ A ∈ E, Measurable fun ω₁ ↦ κ ω₁ A) (h_univ : univ ∈ E) :
    Measurable κ :=
  Measurable.measure_of_isPiSystem hgen hE_pi hκ (hκ univ h_univ)

/-- Remark 8.26: alternatively, if the generating `π`-system `E` contains an increasing sequence
`Eₙ ↑ Ω₂`, then checking the section maps `ω₁ ↦ κ ω₁ A` only on `E` still suffices to prove that
`κ` is measurable. -/
theorem _root_.Measurable.measure_of_isPiSystem_of_exhaustion
    [∀ ω₁, IsFiniteMeasure (κ ω₁)]
    (hgen : ‹MeasurableSpace Ω₂› = MeasurableSpace.generateFrom E) (hE_pi : IsPiSystem E)
    (hκ : ∀ A ∈ E, Measurable fun ω₁ ↦ κ ω₁ A)
    {En : ℕ → Set Ω₂} (hEn_mono : Monotone En) (hEn_mem : ∀ n, En n ∈ E)
    (hEn_spanning : (⋃ n, En n) = univ) :
    Measurable κ := by
  apply Measurable.measure_of_isPiSystem hgen hE_pi hκ
  exact measurable_measure_univ_of_exhaustion hκ hEn_mono hEn_mem hEn_spanning

/- In the probability-measure case, the `univ`-measurability condition is automatic, and the
canonical owner-level specialization is already in mathlib. -/
recall Measurable.measure_of_isPiSystem_of_isProbabilityMeasure

end
