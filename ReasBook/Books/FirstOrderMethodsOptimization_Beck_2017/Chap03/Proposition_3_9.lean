/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.9 is a `bridge/view` statement in the chapter convex-analysis API. Domain
sampling against Definition 3.6, Theorem 3.1, and Theorem 3.3 shows that the relevant owner
surface is already the pair `subdifferential_domain` / `strongDualSubdifferential`, built over the
Chapter 2 owner `effective_domain`; there is no further upstream declaration with the same
conclusion to recall here, so this file should state the proposition directly on that owner API
instead of introducing a parallel wrapper. The literal textbook wording omits the domain condition
`x ∈ subdifferential_domain f`, but that hypothesis is mathematically necessary: if
`x ∉ subdifferential_domain f`, then the subdifferential is empty and hence bounded. The file keeps
that necessary hypothesis explicit in the proposition statement and records the omission only here
in comments. -/
recall effective_domain
recall subdifferential_domain
recall strongDualSubdifferential

/-- Helper for Proposition 3.9: membership in `∂ₛ f(x)` can be checked on `effective_domain f`
through the owner-level subgradient inequality. -/
lemma mem_strongDualSubdifferential_iff_forall_mem_effective_domain
    (f : E → EReal) (x : E) (g : StrongDual ℝ E) :
    g ∈ ∂ₛf(x) ↔
      x ∈ effective_domain f ∧
        ∀ y ∈ effective_domain f,
          f y ≥ f x + (((g : Module.Dual ℝ E) (y - x) : ℝ) : EReal) := by
  -- This is the public rewrite path from the strong-dual bridge back to the owner predicate.
  rw [mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain]

/-- Helper for Proposition 3.9: a strict finrank drop for the direction of
`affineSpan ℝ (effective_domain f)` yields a strong-dual functional that annihilates that
direction and is nonzero somewhere. -/
lemma exists_annihilating_strongDual_of_affineSpan_direction_finrank_lt
    (f : E → EReal)
    (hdim :
      Module.finrank ℝ (affineSpan ℝ (effective_domain f)).direction <
        Module.finrank ℝ E) :
    ∃ z : E, ∃ v : StrongDual ℝ E,
      v z ≠ 0 ∧
        ∀ w ∈ (affineSpan ℝ (effective_domain f)).direction,
          ((v : Module.Dual ℝ E) w : ℝ) = 0 := by
  let p : Submodule ℝ E := (affineSpan ℝ (effective_domain f)).direction
  have hp_lt : p < ⊤ := Submodule.lt_top_of_finrank_lt_finrank hdim
  have hp_ne_top : p ≠ ⊤ := ne_of_lt hp_lt
  -- Pick a vector outside the direction space so that Hahn-Banach-style extension supplies a
  -- dual vector annihilating `p` but not that witness.
  obtain ⟨z, hz⟩ : ∃ z : E, z ∉ p := by
    by_contra h
    apply hp_ne_top
    ext w
    constructor
    · intro hw
      trivial
    · intro _
      by_contra hw
      exact h ⟨w, hw⟩
  obtain ⟨η, hηz, hηker⟩ := Submodule.exists_le_ker_of_notMem hz
  let v : StrongDual ℝ E := LinearMap.toContinuousLinearMap η
  refine ⟨z, v, ?_, ?_⟩
  · -- The chosen witness remains nonzero after passing from the algebraic to the continuous dual.
    simpa [v] using hηz
  · -- Every vector in the direction lies in the kernel of the annihilator.
    intro w hw
    have hwker : w ∈ LinearMap.ker η := hηker hw
    simpa [LinearMap.mem_ker, v] using hwker

/-- Helper for Proposition 3.9: adding a strong-dual functional that vanishes on every admissible
domain difference preserves strong-dual subgradient membership. -/
lemma add_smul_mem_strongDualSubdifferential_of_annihilates_direction
    (f : E → EReal) (x : E) {g v : StrongDual ℝ E}
    (hg : g ∈ ∂ₛf(x))
    (hv : ∀ w ∈ (affineSpan ℝ (effective_domain f)).direction,
      ((v : Module.Dual ℝ E) w : ℝ) = 0)
    (β : ℝ) :
    g + β • v ∈ ∂ₛf(x) := by
  rw [mem_strongDualSubdifferential_iff_forall_mem_effective_domain] at hg ⊢
  rcases hg with ⟨hx, hg⟩
  refine ⟨hx, ?_⟩
  intro y hy
  -- Both points lie in the affine span of the effective domain, so their difference lies in the
  -- corresponding direction subspace where `v` vanishes.
  have hx_aff : x ∈ affineSpan ℝ (effective_domain f) :=
    subset_affineSpan ℝ (effective_domain f) hx
  have hy_aff : y ∈ affineSpan ℝ (effective_domain f) :=
    subset_affineSpan ℝ (effective_domain f) hy
  have hdir : y - x ∈ (affineSpan ℝ (effective_domain f)).direction := by
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hy_aff hx_aff
  have hvzero : ((v : Module.Dual ℝ E) (y - x) : ℝ) = 0 := hv (y - x) hdir
  -- Rewrite the new functional at `y - x`; the extra term disappears because the difference lies
  -- in the annihilated direction space.
  simpa [hvzero, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hg y hy

/-- Helper for Proposition 3.9: an affine line in `StrongDual ℝ E` is unbounded once one
evaluation direction has nonzero slope. -/
lemma not_isBounded_range_add_smul_of_eval_ne_zero
    {g v : StrongDual ℝ E} {z : E} (hz : v z ≠ 0) :
    ¬ IsBounded (Set.range fun β : ℝ => g + β • v) := by
  -- Evaluate the affine line at the witness point; boundedness would descend to a real affine
  -- line with nonzero slope.
  intro hbounded
  have himage :
      IsBounded ((fun h : StrongDual ℝ E ↦ h z) '' Set.range (fun β : ℝ => g + β • v)) :=
    (ContinuousLinearMap.lipschitz_apply z).isBounded_image hbounded
  have himage_eq :
      (fun h : StrongDual ℝ E ↦ h z) '' Set.range (fun β : ℝ => g + β • v) =
        Set.range (fun β : ℝ => g z + β * v z) := by
    ext t
    constructor
    · rintro ⟨h, ⟨β, rfl⟩, rfl⟩
      refine ⟨β, ?_⟩
      simp [smul_eq_mul]
    · rintro ⟨β, rfl⟩
      refine ⟨g + β • v, ⟨β, rfl⟩, ?_⟩
      simp [smul_eq_mul]
  rw [himage_eq] at himage
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp himage
  have hR_nonneg : 0 ≤ R := by
    have hmem : g z ∈ Metric.closedBall (0 : ℝ) R := hR ⟨0, by simp⟩
    have hnorm : ‖g z‖ ≤ R := by
      simpa [Metric.closedBall, dist_eq_norm] using hmem
    exact le_trans (norm_nonneg (g z)) hnorm
  let β : ℝ := (R + |g z| + 1) / v z
  have hβmul : β * v z = R + |g z| + 1 := by
    dsimp [β]
    field_simp [hz]
  have hmem : g z + β * v z ∈ Metric.closedBall (0 : ℝ) R := hR ⟨β, rfl⟩
  have hnorm : ‖g z + β * v z‖ ≤ R := by
    simpa [Metric.closedBall, dist_eq_norm] using hmem
  have hnonneg : 0 ≤ g z + (R + |g z| + 1) := by
    nlinarith [neg_abs_le (g z), hR_nonneg]
  have hgt : R < g z + (R + |g z| + 1) := by
    nlinarith [neg_abs_le (g z)]
  rw [hβmul, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hnorm
  linarith

-- Proof sketch: translating the affine hull of `effective_domain f` by `-x` does not change its
-- affine dimension, so the geometric hypothesis becomes the strict finrank inequality for the
-- direction space of `affineSpan ℝ (effective_domain f)`. If `x ∈ subdifferential_domain f`, then
-- finite dimensionality upgrades an algebraic-dual subgradient at `x` to the continuous-dual
-- bridge `∂ₛ f(x)`. Apply the standard unboundedness argument in codimension
-- at least one on that bridge set.
/-- Proposition 3.9: if the affine hull of the effective domain has direction-space dimension
strictly smaller than the ambient space, equivalently
`Module.finrank ℝ (affineSpan ℝ (effective_domain f)).direction < Module.finrank ℝ E`, then every
point of the owner subdifferential domain `dom(∂ f)` has an unbounded continuous-dual
subdifferential `∂ₛ f(x)`. -/
theorem subdifferential_unbounded_of_affineSpan_effective_domain_direction_finrank_lt
    (f : E → EReal) (x : E)
    (hdim :
      Module.finrank ℝ (affineSpan ℝ (effective_domain f)).direction <
        Module.finrank ℝ E)
    (hx : x ∈ subdifferential_domain f) :
    ¬ IsBounded (∂ₛ f(x)) := by
  -- Start from one owner-level subgradient and move it into the strong dual using finite
  -- dimensionality.
  rcases mem_subdifferential_domain.mp hx with ⟨η, hη⟩
  let g₀ : StrongDual ℝ E := LinearMap.toContinuousLinearMap η
  have hg₀ : g₀ ∈ ∂ₛf(x) := by
    simpa [g₀] using hη
  -- Codimension at least one yields a nontrivial annihilator of the affine-span direction.
  rcases exists_annihilating_strongDual_of_affineSpan_direction_finrank_lt f hdim with
    ⟨z, v, hvz, hvdir⟩
  -- The resulting affine line stays inside `∂ₛ f(x)`, so boundedness of `∂ₛ f(x)` would force
  -- boundedness of that line.
  intro hbounded
  have hline_subset : Set.range (fun β : ℝ => g₀ + β • v) ⊆ ∂ₛf(x) := by
    intro h hh
    rcases hh with ⟨β, rfl⟩
    exact add_smul_mem_strongDualSubdifferential_of_annihilates_direction f x hg₀ hvdir β
  have hline_bounded : IsBounded (Set.range fun β : ℝ => g₀ + β • v) :=
    IsBounded.subset hbounded hline_subset
  exact not_isBounded_range_add_smul_of_eval_ne_zero hvz hline_bounded

end
