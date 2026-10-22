/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open Set
open scoped ENNReal NNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

/-- Helper for Theorem 21.55: bounded variation on `Icc 0 t` transfers to the real interval
`Set.Icc (0 : ℝ) t` after composing with `Real.toNNReal`. -/
private lemma boundedVariationOn_comp_toNNReal_Icc
    {f : NNReal → ℝ} {t : NNReal} (hf : BoundedVariationOn f (Icc 0 t)) :
    BoundedVariationOn (fun s : ℝ ↦ f (Real.toNNReal s)) (Set.Icc (0 : ℝ) t) := by
  rw [BoundedVariationOn] at hf ⊢
  have hmono : MonotoneOn Real.toNNReal (Set.Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    exact Real.toNNReal_monotone hxy
  have himage : Real.toNNReal '' Set.Ici (0 : ℝ) = (Set.univ : Set NNReal) := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      refine ⟨(y : ℝ), ?_, ?_⟩
      · exact_mod_cast y.2
      · simp
  have hcomp :
      eVariationOn (fun s : ℝ ↦ f (Real.toNNReal s)) (Set.Icc (0 : ℝ) t) =
        eVariationOn f (Icc 0 t) := by
    have hinter : Set.Ici (0 : ℝ) ∩ Set.Icc (0 : ℝ) t = Set.Icc (0 : ℝ) t := by
      ext x
      simp
    simpa [Function.comp, himage, hinter] using
      (eVariationOn.comp_inter_Icc_eq_of_monotoneOn
        (f := f) (t := Set.Ici (0 : ℝ)) (φ := Real.toNNReal)
        (x := (0 : ℝ)) (y := (t : ℝ)) hmono (by simp) (by exact_mod_cast t.2))
  rwa [hcomp]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.55: every interior point of `(0, t)` lies in the nondifferentiability
set once the path is known to be nowhere differentiable on `Set.Ici 0`. -/
private lemma ioo_subset_nondifferentiableSet_of_pathwiseIci
    {W : NNReal → Ω → ℝ} {t : NNReal} (ω : Ω)
    (hndiff : ∀ s : NNReal,
      ¬ DifferentiableWithinAt ℝ (fun r : ℝ ↦ W (Real.toNNReal r) ω) (Set.Ici (0 : ℝ))
        (s : ℝ)) :
    Set.Ioo (0 : ℝ) t ⊆
      {x | ¬ DifferentiableAt ℝ (fun r : ℝ ↦ W (Real.toNNReal r) ω) x} := by
  intro x hx
  have hx_nonneg : 0 ≤ x := hx.1.le
  -- Proof comment: on the interior of `(0, t)` the `Real.toNNReal` transport is trivial, so the
  -- imported half-line nowhere-differentiability theorem applies directly.
  have hwithin :
      ¬ DifferentiableWithinAt ℝ (fun r : ℝ ↦ W (Real.toNNReal r) ω) (Set.Ici (0 : ℝ)) x := by
    simpa [Real.toNNReal_of_nonneg hx_nonneg] using hndiff (Real.toNNReal x)
  exact fun hdiffAt ↦ hwithin hdiffAt.differentiableWithinAt

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.55: a bounded-variation Brownian path on `[0, t]` would be
almost-everywhere differentiable on `(0, t)`, contradicting Theorem 21.17. -/
private lemma not_boundedVariationOn_Icc_of_ae_nowhereDifferentiable
    {W : NNReal → Ω → ℝ} {t : NNReal} (ht : 0 < t) (ω : Ω)
    (hndiff : ∀ s : NNReal,
      ¬ DifferentiableWithinAt ℝ (fun r : ℝ ↦ W (Real.toNNReal r) ω) (Set.Ici (0 : ℝ))
        (s : ℝ)) :
    ¬ BoundedVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 t) := by
  intro hf
  let g : ℝ → ℝ := fun s ↦ W (Real.toNNReal s) ω
  have hgvar : BoundedVariationOn g (Set.Icc (0 : ℝ) t) := by
    simpa [g] using boundedVariationOn_comp_toNNReal_Icc hf
  have ht_nonneg : (0 : ℝ) ≤ t := by
    exact_mod_cast ht.le
  have hdiff :
      ∀ᵐ x, x ∈ Set.Ioo (0 : ℝ) t → DifferentiableAt ℝ g x := by
    have hgvar_uIcc : BoundedVariationOn g (Set.uIcc (0 : ℝ) t) := by
      simpa [uIcc_of_le ht_nonneg] using hgvar
    have hdiff_uIcc :
        ∀ᵐ x, x ∈ Set.uIcc (0 : ℝ) t → DifferentiableAt ℝ g x :=
      BoundedVariationOn.ae_differentiableAt_of_mem_uIcc
        (f := g) (a := (0 : ℝ)) (b := t) hgvar_uIcc
    filter_upwards [hdiff_uIcc] with x hx hxt
    have hx_mem : x ∈ Set.uIcc (0 : ℝ) t := by
      simpa [uIcc_of_le ht_nonneg, Set.mem_Icc] using ⟨hxt.1.le, hxt.2.le⟩
    exact hx hx_mem
  have hdiff_restrict :
      ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : ℝ) t), DifferentiableAt ℝ g x := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hdiff
  have hnotdiff_measure :
      (volume.restrict (Set.Ioo (0 : ℝ) t)) {x | ¬ DifferentiableAt ℝ g x} = 0 := by
    rw [← ae_iff]
    exact hdiff_restrict
  have hsubset : Set.Ioo (0 : ℝ) t ⊆ {x | ¬ DifferentiableAt ℝ g x} := by
    simpa [g] using ioo_subset_nondifferentiableSet_of_pathwiseIci (W := W) (t := t) ω hndiff
  have hIoo_zero : volume (Set.Ioo (0 : ℝ) t) = 0 := by
    have hle :
        volume (Set.Ioo (0 : ℝ) t) ≤
          (volume.restrict (Set.Ioo (0 : ℝ) t)) {x | ¬ DifferentiableAt ℝ g x} := by
      simpa [Measure.restrict_apply, measurableSet_Ioo, Set.inter_self] using
        (measure_mono hsubset :
          (volume.restrict (Set.Ioo (0 : ℝ) t)) (Set.Ioo (0 : ℝ) t) ≤
            (volume.restrict (Set.Ioo (0 : ℝ) t)) {x | ¬ DifferentiableAt ℝ g x})
    exact le_antisymm (hle.trans_eq hnotdiff_measure) (by simp)
  have hIoo_pos : 0 < volume (Set.Ioo (0 : ℝ) t) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by simpa using (show (0 : ℝ) < t by exact_mod_cast ht))
  exact hIoo_pos.ne' hIoo_zero

/-- Theorem 21.55: for a Brownian motion `W`, the total variation of almost every sample path on
each initial interval `[0, t]` with `t > 0` is infinite. -/
theorem ae_infiniteVariationOn_Icc
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {t : NNReal} (ht : 0 < t) :
    ∀ᵐ ω ∂μ, eVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 t) = ∞ := by
  -- Route correction: use the compiled Theorem 21.17 owner theorem rather than duplicating its
  -- dyadic block-event bridge inside this file.
  have hndiff := hW.ae_nowhere_differentiable_path
  filter_upwards [hndiff] with ω hω
  -- Proof comment: finite variation on `[0, t]` would force almost-everywhere differentiability
  -- on `(0, t)`, contradicting the nowhere-differentiability theorem.
  have hnot :
      ¬ BoundedVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 t) :=
    not_boundedVariationOn_Icc_of_ae_nowhereDifferentiable ht ω hω
  simpa [BoundedVariationOn] using hnot

/-- For Brownian motion, almost every sample path fails the chapter's canonical local-finite-
variation owner property `LocallyBoundedVariationOn ... univ`. This is the owner-level reformulation
of Theorem 21.55 via Definition 21.52. -/
theorem ae_not_locallyBoundedVariationOn_univ
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W) :
    ∀ᵐ ω ∂μ, ¬ LocallyBoundedVariationOn (fun s : NNReal ↦ W s ω) univ := by
  have hunit :
      ∀ᵐ ω ∂μ, eVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 (1 : NNReal)) = ∞ :=
    hW.ae_infiniteVariationOn_Icc zero_lt_one
  filter_upwards [hunit] with ω htop
  intro hloc
  have hfinite : BoundedVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 (1 : NNReal)) := by
    simpa using hloc 0 1 (by simp) (by simp)
  exact hfinite htop

end IsBrownianMotion

end ProbabilityTheory
