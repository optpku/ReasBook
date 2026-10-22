/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter Topology

variable {E : Type u} [MetricSpace E] {f : E → ℝ} {fSeq : ℕ → E → ℝ}

/- Lemma 15.22 (1): If `fₙ : E → ℝ` converges pointwise to `f` and the family `(fₙ)` is
uniformly equicontinuous, then the limit `f` is uniformly continuous. This is exactly the
canonical owner theorem `Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous`. -/
recall Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous

-- Proof sketch: restrict the family to the compact set `K`; uniform equicontinuity gives
-- equicontinuity there, and on a compact domain Ascoli identifies pointwise convergence with
-- uniform convergence.
/-- Lemma 15.22 (2): If `fₙ : E → ℝ` converges pointwise to `f` and `(fₙ)` is uniformly
equicontinuous, then the convergence is uniform on every compact set `K ⊆ E`. -/
theorem tendstoUniformlyOn_of_pointwise_of_uniformEquicontinuous
    (h_pointwise : ∀ x, Filter.Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x)))
    (h_eqcont : UniformEquicontinuous fSeq) {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x ↦ fSeq n x) f atTop K := by
  let 𝔖 : Set (Set E) := {K}
  have h𝔖 : ⋃₀ 𝔖 = K := by
    simp [𝔖]
  have h_restrict : Tendsto ((⋃₀ 𝔖).restrict ∘ fSeq) atTop (𝓝 ((⋃₀ 𝔖).restrict f)) := by
    rw [h𝔖, tendsto_pi_nhds]
    intro x
    exact h_pointwise x
  have h_uniform :
      Tendsto (UniformOnFun.ofFun 𝔖 ∘ fSeq) atTop (𝓝 <| UniformOnFun.ofFun 𝔖 f) := by
    refine (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' ?_ ?_ atTop f).2 h_restrict
    · intro L hL
      rcases Set.mem_singleton_iff.mp (by simpa [𝔖] using hL) with rfl
      simpa using hK
    · intro L hL
      simpa [𝔖] using h_eqcont.equicontinuous.equicontinuousOn L
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at h_uniform
  simpa [𝔖] using h_uniform K (by simp [𝔖])
