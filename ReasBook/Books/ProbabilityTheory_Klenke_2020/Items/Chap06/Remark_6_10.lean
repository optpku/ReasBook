/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {β : Type v} [NormedAddCommGroup β]

-- Proof sketch: unpack the two `TendstoInMean` hypotheses into convergence statements in the
-- canonical `L¹(μ)` space. The sequence terms represent the same functions, so `MemLp.toLp_congr`
-- identifies the two `L¹`-valued sequences and `tendsto_nhds_unique` forces the limits to agree.
-- The almost-everywhere conclusion is then the canonical reformulation via
-- `MemLp.toLp_eq_toLp_iff`.
/-- Remark 6.10: if a sequence converges in mean to both `f` and `g`, then `f` and `g` are equal
`μ`-almost everywhere. -/
theorem ae_eq_of_tendstoInMean {fSeq : ℕ → Ω → β} {f g : Ω → β}
    (h_f : TendstoInMean μ fSeq f) (h_g : TendstoInMean μ fSeq g) :
    f =ᵐ[μ] g := by
  rcases h_f with ⟨h_memLpSeq_f, h_memLp_f, h_tendsto_f⟩
  rcases h_g with ⟨h_memLpSeq_g, h_memLp_g, h_tendsto_g⟩
  have h_seq :
      (fun n ↦ (h_memLpSeq_f n).toLp (fSeq n)) = fun n ↦ (h_memLpSeq_g n).toLp (fSeq n) := by
    funext n
    exact MemLp.toLp_congr (h_memLpSeq_f n) (h_memLpSeq_g n) Filter.EventuallyEq.rfl
  have h_eq : h_memLp_f.toLp f = h_memLp_g.toLp g := by
    exact tendsto_nhds_unique h_tendsto_f (h_seq.symm ▸ h_tendsto_g)
  exact (MemLp.toLp_eq_toLp_iff h_memLp_f h_memLp_g).mp h_eq

/-- If a sequence converges in mean to both `f` and `g`, then their canonical images in `L¹(μ)`
coincide. -/
theorem toL1_eq_of_tendstoInMean {fSeq : ℕ → Ω → β} {f g : Ω → β}
    (h_f : TendstoInMean μ fSeq f) (h_g : TendstoInMean μ fSeq g) :
    h_f.integrable.toL1 f = h_g.integrable.toL1 g :=
  (Integrable.toL1_eq_toL1_iff f g h_f.integrable h_g.integrable).2 <|
    ae_eq_of_tendstoInMean h_f h_g
