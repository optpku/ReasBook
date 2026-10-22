/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Filter
open scoped Topology

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Text 2.0.14 (1): a map on a subset of a real Hilbert space is weakly continuous when it is
continuous from the weak subspace topology on the domain to the weak topology on the codomain. -/
def WeaklyContinuous {D : Set H} (T : D → K) : Prop :=
  letI : TopologicalSpace D :=
    TopologicalSpace.induced (fun x : D ↦ toWeakSpace ℝ H x) inferInstance
  Continuous fun x : D ↦ toWeakSpace ℝ K (T x)

-- Proof sketch: unfold `WeaklyContinuous`; continuity for the subtype of `WeakSpace ℝ H` is
-- equivalent to preservation of `atTop`-convergent directed nets in that weak subspace topology.
/-- Weak continuity on a subset is equivalent to preservation of weak convergence along every
directed net in that subset. -/
theorem weaklyContinuous_iff_forall_net_tendsto {D : Set H} {T : D → K} :
    WeaklyContinuous T ↔
      ∀ {A : Type w} [Preorder A] [IsDirectedOrder A] (ξ : A → D) (x : D),
        Tendsto
            (fun a ↦ toWeakSpace ℝ H (ξ a : H))
            atTop
            (𝓝 (toWeakSpace ℝ H (x : H))) →
          Tendsto
            (fun a ↦ toWeakSpace ℝ K (T (ξ a)))
            atTop
            (𝓝 (toWeakSpace ℝ K (T x))) := sorry

/-- Text 2.0.14 (2): an extended-real-valued function is weakly lower semicontinuous at `x` when
it is lower semicontinuous at `x` for the weak topology on the Hilbert space. -/
def WeaklyLowerSemicontinuousAt (f : H → EReal) (x : H) : Prop :=
  LowerSemicontinuousAt (f ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H x)

-- Proof sketch: rewrite weak lower semicontinuity at `x` as lower semicontinuity at the point
-- `toWeakSpace ℝ H x`, then apply the canonical liminf characterization in the weak topology.
/-- Weak lower semicontinuity at a point is equivalent to the liminf inequality along every weakly
convergent directed net. -/
theorem weaklyLowerSemicontinuousAt_iff_forall_net_le_liminf
    (f : H → EReal) (x : H) :
    WeaklyLowerSemicontinuousAt f x ↔
      ∀ {A : Type w} [Preorder A] [IsDirectedOrder A] (ξ : A → H),
        Tendsto
            (fun a ↦ toWeakSpace ℝ H (ξ a))
            atTop
            (𝓝 (toWeakSpace ℝ H x)) →
          f x ≤ Filter.liminf (fun a ↦ f (ξ a)) atTop := sorry

/-- Text 2.0.14 (3): an extended-real-valued function is weakly lower semicontinuous when it is
lower semicontinuous for the weak topology on the Hilbert space. -/
def WeaklyLowerSemicontinuous (f : H → EReal) : Prop :=
  LowerSemicontinuous (f ∘ (toWeakSpace ℝ H).symm)

-- Proof sketch: this is the canonical theorem `lowerSemicontinuous_iff`, applied to the function
-- on `WeakSpace ℝ H` induced by `f`.
/-- Global weak lower semicontinuity is equivalent to pointwise weak lower semicontinuity. -/
theorem weaklyLowerSemicontinuous_iff_forall_weaklyLowerSemicontinuousAt
    (f : H → EReal) :
    WeaklyLowerSemicontinuous f ↔ ∀ x, WeaklyLowerSemicontinuousAt f x := by
  simpa [WeaklyLowerSemicontinuous, WeaklyLowerSemicontinuousAt] using
    (lowerSemicontinuous_iff :
      LowerSemicontinuous (f ∘ (toWeakSpace ℝ H).symm) ↔
        ∀ x : WeakSpace ℝ H,
          LowerSemicontinuousAt (f ∘ (toWeakSpace ℝ H).symm) x)
