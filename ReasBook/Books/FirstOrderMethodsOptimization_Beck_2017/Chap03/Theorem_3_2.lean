/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.2 is `source-facing` in finite-dimensional convex geometry. Its owner abstractions are
Mathlib's separation theorem `geometric_hahn_banach_of_nonempty_interior_point`, together with the
finite-dimensional affine-span and dual-annihilator API. The primitive data are only the convex set
`C` and the comparison point `y`; the supporting functional is derived from those owner
constructions rather than stored through any local wrapper. -/

-- Proof sketch: if `interior C` is nonempty, apply
-- `geometric_hahn_banach_of_nonempty_interior_point` directly. If `interior C = ∅`, then
-- `affineSpan ℝ C` is proper. When `y ∉ affineSpan ℝ C`, strictly separate `y` from that closed
-- affine subspace. When `y ∈ affineSpan ℝ C`, choose a nonzero functional in the dual
-- annihilator of the direction of `affineSpan ℝ C`; it is constant on the affine span, hence on
-- `C`, so its value on `C` equals its value at `y`.
/-- Theorem 3.2: supporting hyperplane theorem. A nonempty convex set and a point outside its
interior admit a nonzero continuous linear functional whose value on the set is bounded above by
its value at the point. -/
theorem supporting_hyperplane_of_not_mem_interior {C : Set E} {y : E} (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C) (hy : y ∉ interior C) :
    ∃ p : StrongDual ℝ E, p ≠ 0 ∧ ∀ x ∈ C, p x ≤ p y := by
  by_cases hCint : (interior C).Nonempty
  · exact geometric_hahn_banach_of_nonempty_interior_point hC_convex hy hCint
  · let A : AffineSubspace ℝ E := affineSpan ℝ C
    have hA_nonempty : (A : Set E).Nonempty := by
      rcases hC_nonempty with ⟨x, hx⟩
      exact ⟨x, by simpa [A] using subset_affineSpan ℝ C hx⟩
    by_cases hyA : y ∈ A
    · have hdir_ne_top : A.direction ≠ (⊤ : Submodule ℝ E) := by
        intro hdir
        have htop : A = (⊤ : AffineSubspace ℝ E) :=
          (AffineSubspace.direction_eq_top_iff_of_nonempty hA_nonempty).1 hdir
        exact hCint ((hC_convex.interior_nonempty_iff_affineSpan_eq_top).2 (by simpa [A] using htop))
      have hann_ne_bot :
          A.direction.dualAnnihilator ≠ (⊥ : Submodule ℝ (Module.Dual ℝ E)) := by
        intro hann
        exact hdir_ne_top ((Submodule.dualAnnihilator_eq_bot_iff).1 hann)
      obtain ⟨φ, hφmem, hφne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hann_ne_bot
      refine ⟨LinearMap.toContinuousLinearMap φ, ?_, ?_⟩
      · exact fun hzero ↦
          hφne ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).injective hzero)
      · intro x hx
        have hxA : x ∈ A := by simpa [A] using subset_affineSpan ℝ C hx
        have hxy_dir : x - y ∈ A.direction := by
          simpa using A.vsub_mem_direction hxA hyA
        have hxy_zero : φ (x - y) = 0 :=
          (Submodule.mem_dualAnnihilator φ).1 hφmem _ hxy_dir
        have hxy_eq : φ x = φ y := sub_eq_zero.mp (by simpa using hxy_zero)
        simp [hxy_eq]
    · obtain ⟨p, α, hpA, hpy⟩ :=
        geometric_hahn_banach_closed_point A.convex A.closed_of_finiteDimensional hyA
      obtain ⟨x₀, hx₀⟩ := hC_nonempty
      refine ⟨p, ?_, fun x hx ↦ (hpA x (by simpa [A] using subset_affineSpan ℝ C hx)).le.trans hpy.le⟩
      intro hp0
      have h0lt : (0 : ℝ) < α := by
        simpa [A, hp0] using hpA x₀ (by simpa [A] using subset_affineSpan ℝ C hx₀)
      have hαlt : α < 0 := by
        simpa [hp0] using hpy
      exact (not_lt_of_ge h0lt.le hαlt).elim

end
