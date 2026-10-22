/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Order.Filter.AtTopBot.Archimedean

public section

universe u

open Filter

variable {H : Type u} [SeminormedAddCommGroup H]

instance instIsCountablyGeneratedCobounded : (Bornology.cobounded H).IsCountablyGenerated := by
  let h :
      (atTop : Filter ℝ).HasCountableBasis (fun _ : ℕ ↦ True) fun n ↦ Set.Ici n :=
    atTop_hasCountableBasis_of_archimedean
  exact (HasBasis.cobounded_of_norm h.toHasBasis).isCountablyGenerated

/-- Definition 2.29. A functional `J : H → ℝ` is coercive if `J (f n) → ∞`
whenever `‖f n‖ → ∞`. -/
def coercive (J : H → ℝ) : Prop :=
  Tendsto J (Bornology.cobounded H) atTop

/-- A coercive functional sends every filter escaping to infinity in `H` to `atTop` in `ℝ`. -/
theorem coercive.tendsto_comp {J : H → ℝ} (hJ : coercive J) {α : Type*} {l : Filter α} {f : α → H}
    (hf : Tendsto f l (Bornology.cobounded H)) : Tendsto (fun a ↦ J (f a)) l atTop :=
  hJ.comp hf

/-- Rewrites `coercive` as the source sequence criterion for sequences escaping to
infinity in norm. -/
theorem coercive_iff {J : H → ℝ} :
    coercive J ↔
      ∀ {f : ℕ → H},
        Tendsto (fun n ↦ ‖f n‖) atTop atTop → Tendsto (fun n ↦ J (f n)) atTop atTop := by
  rw [coercive, tendsto_iff_seq_tendsto]
  constructor
  · intro hJ f hf
    simpa [Function.comp_def] using hJ f ((tendsto_norm_atTop_iff_cobounded).1 hf)
  · intro hJ f hf
    simpa [Function.comp_def] using hJ ((tendsto_norm_atTop_iff_cobounded).2 hf)
