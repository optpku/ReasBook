/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped Topology

/- The textbook notion that `T : H → K` is Fréchet differentiable at an interior point `x` of
`C` with derivative `T'` is formalized by the canonical predicate `HasFDerivWithinAt T T' C x`;
the interior-point assumption itself is recorded separately as `x ∈ interior C`. -/
recall HasFDerivWithinAt

section

variable
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {K : Type w} [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- Definition 2.56: a bounded operator `T''` is a second Fréchet derivative of `T` at `x` within
`C` if it is the derivative at `x` of a first-derivative map defined on some neighborhood of `x`
contained in `C`. -/
def HasSecondFrechetDerivWithinAt
    (𝕜 : Type u) [NontriviallyNormedField 𝕜]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {K : Type w} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    (T : H → K) (C : Set H) (x : H) (T'' : H →L[𝕜] H →L[𝕜] K) : Prop :=
  ∃ U : Set H, U ∈ 𝓝 x ∧ U ⊆ C ∧
    ∃ T' : H → H →L[𝕜] K,
      (∀ y ∈ U, HasFDerivWithinAt T (T' y) U y) ∧
      HasFDerivWithinAt T' T'' U x

/-- Unfolding `HasSecondFrechetDerivWithinAt` amounts to the existence of a neighborhood of `x`
contained in `C` together with a first-derivative map for `T` on that neighborhood whose
derivative at `x` is `T''`. -/
theorem hasSecondFrechetDerivWithinAt_iff
    {T : H → K} {C : Set H} {x : H} {T'' : H →L[𝕜] H →L[𝕜] K} :
    HasSecondFrechetDerivWithinAt 𝕜 T C x T'' ↔
      ∃ U : Set H, U ∈ 𝓝 x ∧ U ⊆ C ∧
        ∃ T' : H → H →L[𝕜] K,
          (∀ y ∈ U, HasFDerivWithinAt T (T' y) U y) ∧
          HasFDerivWithinAt T' T'' U x :=
  Iff.rfl

/-- Being twice Fréchet differentiable at `x` within `C` means admitting some second Fréchet
derivative there. -/
def TwiceFrechetDifferentiableWithinAt
    (𝕜 : Type u) [NontriviallyNormedField 𝕜]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {K : Type w} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    (T : H → K) (C : Set H) (x : H) : Prop :=
  ∃ T'' : H →L[𝕜] H →L[𝕜] K, HasSecondFrechetDerivWithinAt 𝕜 T C x T''

/-- Existence of a second Fréchet derivative is exactly twice Fréchet differentiability. -/
theorem twiceFrechetDifferentiableWithinAt_iff_exists_hasSecondFrechetDerivWithinAt
    {T : H → K} {C : Set H} {x : H} :
    TwiceFrechetDifferentiableWithinAt 𝕜 T C x ↔
      ∃ T'' : H →L[𝕜] H →L[𝕜] K, HasSecondFrechetDerivWithinAt 𝕜 T C x T'' :=
  Iff.rfl

/-- A global `C²` map is twice Fréchet differentiable on the whole space in the sense of
Definition 2.56. -/
theorem ContDiff.twiceFrechetDifferentiableWithinAt_univ
    {T : H → K} (hT : ContDiff 𝕜 2 T) (x : H) :
    TwiceFrechetDifferentiableWithinAt 𝕜 T Set.univ x := by
  have hDiff : Differentiable 𝕜 T := hT.differentiable (by norm_num)
  have hFDeriv : ContDiff 𝕜 1 (fderiv 𝕜 T) := by
    have hSucc : ContDiff 𝕜 (1 + 1) T := by
      simpa using hT
    exact (contDiff_succ_iff_fderiv.1 hSucc).2.2
  have hDiffFDeriv : Differentiable 𝕜 (fderiv 𝕜 T) := hFDeriv.differentiable_one
  refine ⟨fderiv 𝕜 (fderiv 𝕜 T) x, Set.univ, by simp, by simp, fderiv 𝕜 T, ?_, ?_⟩
  · intro y hy
    exact (hDiff y).hasFDerivAt.hasFDerivWithinAt
  · exact (hDiffFDeriv x).hasFDerivAt.hasFDerivWithinAt

end
