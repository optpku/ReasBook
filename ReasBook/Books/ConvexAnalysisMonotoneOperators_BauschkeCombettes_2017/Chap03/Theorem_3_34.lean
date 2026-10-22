/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Theorem 3.34: weak sequential closedness of the weak-space image pulls back to
strong sequential closedness of the original set. -/
-- Proof sketch: a strongly convergent sequence becomes weakly convergent after applying the
-- canonical continuous map `toWeakSpace`, so sequential closedness of the weak image descends
-- along the injective preimage.
private lemma isSeqClosed_of_weak_image_isSeqClosed {C : Set 𝓗}
    (hC : IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C)) :
    IsSeqClosed C := by
  -- Pull back sequential closedness along the sequentially continuous map to the weak space.
  have hcont : Continuous (toWeakSpace ℝ 𝓗 : 𝓗 → WeakSpace ℝ 𝓗) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ 𝓗).continuous
  simpa [Set.preimage_image_eq _ (toWeakSpace ℝ 𝓗).injective] using hC.preimage hcont.seqContinuous

/-- Helper for Theorem 3.34: a closed convex set has weakly closed image in the weak space. -/
-- Proof sketch: `Convex.toWeakSpace_closure` identifies the weak closure of the image with the
-- image of the strong closure, and closedness makes the latter equal to the original image.
private lemma weak_image_isClosed_of_isClosed_convex {C : Set 𝓗}
    (hC_convex : Convex ℝ C) (hC_closed : IsClosed C) :
    IsClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  -- Rewrite the weak closure of the image as the image of the strong closure.
  rw [← closure_eq_iff_isClosed]
  calc
    closure ((toWeakSpace ℝ 𝓗) '' C) = (toWeakSpace ℝ 𝓗) '' closure C := by
      simpa using (hC_convex.toWeakSpace_closure ℝ).symm
    _ = (toWeakSpace ℝ 𝓗) '' C := by
      rw [hC_closed.closure_eq]

/-- Helper for Theorem 3.34: weak closedness of the weak-space image forces strong closedness of
the original convex set. -/
-- Proof sketch: if `x ∈ closure C`, then `toWeakSpace x` lies in the weak closure of the image;
-- weak closedness returns a witness from `C`, and injectivity of `toWeakSpace` identifies it
-- with `x`.
private lemma isClosed_of_weak_image_isClosed_convex {C : Set 𝓗}
    (hC_convex : Convex ℝ C) (hC_weakClosed : IsClosed ((toWeakSpace ℝ 𝓗) '' C)) :
    IsClosed C := by
  -- It suffices to prove that every point in `closure C` already lies in `C`.
  rw [← closure_eq_iff_isClosed]
  refine le_antisymm ?_ subset_closure
  intro x hx
  -- Transport the closure membership to the weak space using the convex closure identity.
  have hxWeak : toWeakSpace ℝ 𝓗 x ∈ closure ((toWeakSpace ℝ 𝓗) '' C) := by
    rw [← hC_convex.toWeakSpace_closure ℝ]
    exact ⟨x, hx, rfl⟩
  -- Weak closedness yields a witness in the image of `C`.
  rw [hC_weakClosed.closure_eq] at hxWeak
  rcases hxWeak with ⟨y, hyC, hyx⟩
  -- Injectivity of `toWeakSpace` pulls the witness back to the original space.
  exact (toWeakSpace ℝ 𝓗).injective hyx ▸ hyC

/-- Theorem 3.34, weak-closedness form: for a convex subset `C` of a real inner-product space,
`C` is closed exactly when its image in `WeakSpace ℝ 𝓗` is weakly closed. -/
theorem isClosed_iff_weak_image_isClosed_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C) :
    IsClosed C ↔ IsClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  refine ⟨weak_image_isClosed_of_isClosed_convex hC_convex,
    isClosed_of_weak_image_isClosed_convex hC_convex⟩

/-- Theorem 3.34, weak-sequential form: for a convex subset `C` of a real inner-product space,
`C` is sequentially closed exactly when its image in `WeakSpace ℝ 𝓗` is weakly sequentially
closed. -/
theorem isSeqClosed_iff_weak_image_isSeqClosed_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C) :
    IsSeqClosed C ↔ IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  refine ⟨?_, isSeqClosed_of_weak_image_isSeqClosed⟩
  intro hC_seqClosed
  have hC_closed : IsClosed C :=
    (isSeqClosed_iff_isClosed : IsSeqClosed C ↔ IsClosed C).1 hC_seqClosed
  exact ((isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed).isSeqClosed

/-- Theorem 3.34: for a convex subset `C` of a real inner-product space, weak sequential closedness,
strong sequential closedness, strong closedness, and weak closedness are equivalent. The weak
conditions are expressed on the image of `C` in `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: `(i) → (ii)` because norm convergence implies weak convergence. `(ii) ↔ (iii)`
-- because the norm topology is metrizable, hence sequential. `(iii) → (iv)` by the Hilbert-space
-- projection argument for closed convex sets, which shows weak limits of points of `C` remain in
-- `C`. `(iv) → (i)` because every weakly closed set is weakly sequentially closed.
theorem convex_weaklySeqClosed_sequentiallyClosed_closed_weaklyClosed_tfae
    {C : Set 𝓗} (hC_convex : Convex ℝ C) :
    List.TFAE
      [IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C),
        IsSeqClosed C,
        IsClosed C,
        IsClosed ((toWeakSpace ℝ 𝓗) '' C)] := by
  -- The sequentially closed strong and weak-space formulations are equivalent for convex sets.
  tfae_have 1 ↔ 2 := by
    simpa [iff_comm] using isSeqClosed_iff_weak_image_isSeqClosed_of_convex hC_convex
  -- In a Hilbert space, the norm topology is metric, so closedness and sequential closedness agree.
  tfae_have 2 ↔ 3 := by
    simpa using (isSeqClosed_iff_isClosed : IsSeqClosed C ↔ IsClosed C)
  -- Convexity identifies strong closedness with weak closedness after transport to `WeakSpace`.
  tfae_have 3 ↔ 4 := by
    exact isClosed_iff_weak_image_isClosed_of_convex hC_convex
  tfae_finish
