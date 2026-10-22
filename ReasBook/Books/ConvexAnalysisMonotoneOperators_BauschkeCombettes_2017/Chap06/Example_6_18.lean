/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_24

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace Topology

universe u

namespace Set

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The dyadically scaled range `\{2^{-n} e_n : n \in \mathbb{N}\}` attached to a sequence in a
real vector space. The signed closed hull from Example 6.18 is canonically
`closedAbsConvexHull ℝ (dyadicScaledRange e)`. -/
def dyadicScaledRange (e : ℕ → E) : Set E :=
  Set.range (fun n ↦ ((2 : ℝ)⁻¹ ^ n) • e n)

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Example 6.18: for a sequence `(e_n)`, let `S` be the closure of the convex hull of the
dyadically scaled points `± 2^{-n} e_n`. Using the canonical owner
`closedAbsConvexHull ℝ (dyadicScaledRange e)` for that symmetric closed hull, let `C = S + S^⊥`,
represented here by
`dyadicSignedCylinder e`. The orthonormality assumptions from the textbook enter only in the later
theorems about this set. -/
def dyadicSignedCylinder (e : ℕ → 𝓗) : Set 𝓗 :=
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  S + S^⊥

/-- Helper for Example 6.18: orthogonality to a set agrees with orthogonality to the closed span of
that set. -/
lemma orthogonalSet_eq_closedSpan_orthogonal (S : Set 𝓗) :
    S^⊥ = (((Submodule.span ℝ S).topologicalClosure)ᗮ : Set 𝓗) := by
  ext u
  constructor
  · intro hu
    have hu_span : u ∈ (Submodule.span ℝ S)ᗮ := by
      rw [Submodule.mem_orthogonal]
      rw [mem_orthogonalSet] at hu
      intro x hx
      -- Extend orthogonality from the generators to their span by linearity of the inner product.
      refine Submodule.span_induction
        (fun y hy ↦ hu y hy)
        (by simp)
        (fun y z _ _ hy hz ↦ by simp [inner_add_left, hy, hz])
        (fun a y _ hy ↦ by simp [inner_smul_left, hy])
        hx
    simpa [Submodule.orthogonal_closure] using hu_span
  · intro hu
    rw [Submodule.orthogonal_closure] at hu
    rw [mem_orthogonalSet]
    intro x hx
    exact ((Submodule.span ℝ S).mem_orthogonal u).mp hu x (Submodule.subset_span hx)

-- Proof sketch: `closedAbsConvexHull ℝ (dyadicScaledRange e)` is absolutely convex, hence convex,
-- and its orthogonal set is the orthogonal complement of a closed subspace, hence convex. The
-- pointwise sum of two convex sets is convex.
/-- The dyadic signed cylinder is convex. -/
theorem dyadicSignedCylinder_convex (e : ℕ → 𝓗) :
    Convex ℝ (dyadicSignedCylinder e) := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  have hS_convex : Convex ℝ S :=
    (absConvex_convexClosedHull (𝕜 := ℝ) (s := dyadicScaledRange e)).2
  have hSorth_convex : Convex ℝ (S^⊥) := by
    -- Replace the orthogonal set by a submodule orthogonal complement.
    rw [orthogonalSet_eq_closedSpan_orthogonal (S := S)]
    exact ((Submodule.span ℝ S).topologicalClosureᗮ).convex
  -- Add the convex hull part and the orthogonal part.
  simpa [dyadicSignedCylinder, S] using hS_convex.add hSorth_convex

-- Proof sketch: `dyadicScaledRange e` is nonempty, so `0` belongs to
-- `closedAbsConvexHull ℝ (dyadicScaledRange e)` by absolute convexity and hence to the cylinder.
/-- The dyadic signed cylinder contains the origin. -/
theorem zero_mem_dyadicSignedCylinder (e : ℕ → 𝓗) :
    (0 : 𝓗) ∈ dyadicSignedCylinder e := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  have hS_bal : Balanced ℝ S :=
    (absConvex_convexClosedHull (𝕜 := ℝ) (s := dyadicScaledRange e)).1
  have hRange_nonempty : (dyadicScaledRange e).Nonempty := by
    refine ⟨e 0, ?_⟩
    exact ⟨0, by simp⟩
  have hS_nonempty : S.Nonempty := hRange_nonempty.mono subset_closedAbsConvexHull
  have hS_zero : (0 : 𝓗) ∈ S := hS_bal.zero_mem hS_nonempty
  have horth_zero : (0 : 𝓗) ∈ S^⊥ := by
    -- The zero vector is orthogonal to every point.
    rw [mem_orthogonalSet]
    intro x hx
    simp
  -- Realize `0` as `0 + 0`.
  simpa [dyadicSignedCylinder, S] using Set.mem_add.mpr ⟨0, hS_zero, 0, horth_zero, by simp⟩

/-- Helper for Example 6.18: the dyadic generating set is nonempty. -/
lemma dyadicScaledRange_nonempty (e : ℕ → 𝓗) :
    (dyadicScaledRange e).Nonempty := by
  refine ⟨e 0, ?_⟩
  refine ⟨0, ?_⟩
  simp

/-- Helper for Example 6.18: the symmetric closed hull of the dyadic generators contains the
origin. -/
lemma zero_mem_closedAbsConvexHull_dyadicScaledRange (e : ℕ → 𝓗) :
    (0 : 𝓗) ∈ closedAbsConvexHull ℝ (dyadicScaledRange e) := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  have hS_bal : Balanced ℝ S :=
    (absConvex_convexClosedHull (𝕜 := ℝ) (s := dyadicScaledRange e)).1
  have hS_nonempty : S.Nonempty := (dyadicScaledRange_nonempty e).mono subset_closedAbsConvexHull
  -- Balanced nonempty sets always contain the origin.
  exact hS_bal.zero_mem hS_nonempty

/-- Helper for Example 6.18: the dyadic base hull sits inside the dyadic signed cylinder. -/
lemma dyadicSignedCylinder_base_hull_subset (e : ℕ → 𝓗) :
    closedAbsConvexHull ℝ (dyadicScaledRange e) ⊆ dyadicSignedCylinder e := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  intro x hx
  have hzero_orth : (0 : 𝓗) ∈ S^⊥ := by
    -- The orthogonal summand always contains the zero vector.
    rw [mem_orthogonalSet]
    intro y hy
    simp
  have hx_add : x ∈ S + S^⊥ := by
    -- Realize a point of the base hull as `x + 0`.
    refine Set.mem_add.mpr ?_
    refine ⟨x, hx, 0, hzero_orth, ?_⟩
    simp
  simpa [dyadicSignedCylinder, S] using hx_add

/-- Helper for Example 6.18: the dyadic cylinder is symmetric with respect to the origin. -/
lemma dyadicSignedCylinder_eq_neg (e : ℕ → 𝓗) :
    dyadicSignedCylinder e = -dyadicSignedCylinder e := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  have hS_bal : Balanced ℝ S :=
    (absConvex_convexClosedHull (𝕜 := ℝ) (s := dyadicScaledRange e)).1
  ext x
  constructor
  · intro hx
    have hx' : x ∈ S + S^⊥ := by simpa [dyadicSignedCylinder, S] using hx
    rcases hx' with ⟨s, hs, u, hu, hsum⟩
    rw [Set.mem_neg]
    change -x ∈ S + S^⊥
    -- Negate both witnesses inside the symmetric hull and the orthogonal set.
    refine Set.mem_add.mpr ?_
    refine ⟨-s, ?_, -u, ?_, ?_⟩
    · simpa using hS_bal.smul_mem (by norm_num : ‖(-1 : ℝ)‖ ≤ 1) hs
    · rw [mem_orthogonalSet] at hu ⊢
      intro y hy
      simpa [inner_neg_right] using congrArg Neg.neg (hu y hy)
    · simpa [add_comm] using congrArg Neg.neg hsum
  · intro hx
    have hx' : -x ∈ S + S^⊥ := by
      rw [Set.mem_neg] at hx
      simpa [dyadicSignedCylinder, S] using hx
    rcases hx' with ⟨s, hs, u, hu, hsum⟩
    change x ∈ S + S^⊥
    refine Set.mem_add.mpr ?_
    refine ⟨-s, ?_, -u, ?_, ?_⟩
    · simpa using hS_bal.smul_mem (by norm_num : ‖(-1 : ℝ)‖ ≤ 1) hs
    · rw [mem_orthogonalSet] at hu ⊢
      intro y hy
      simpa [inner_neg_right] using congrArg Neg.neg (hu y hy)
    · simpa [add_comm] using congrArg Neg.neg hsum

/-- Helper for Example 6.18: the closed absolutely convex hull of the dyadic generators lies in
the expected inner-product slab. -/
lemma closedAbsConvexHull_subset_dyadic_inner_slab (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (m : ℕ) :
    closedAbsConvexHull ℝ (dyadicScaledRange e) ⊆
      {x : 𝓗 | |⟪x, e m⟫_ℝ| ≤ ((2 : ℝ)⁻¹) ^ m} := by
  let r : ℝ := ((2 : ℝ)⁻¹) ^ m
  let slab : Set 𝓗 := {x : 𝓗 | |⟪x, e m⟫_ℝ| ≤ r}
  refine closedAbsConvexHull_min ?_ ?_ ?_
  · intro x hx
    rcases hx with ⟨n, rfl⟩
    by_cases hnm : n = m
    · subst n
      -- On the distinguished generator, the bound is an equality.
      simp [real_inner_smul_left, he.norm_eq_one, abs_of_nonneg]
    · -- Off the distinguished index, orthonormality kills the inner product.
      simp [real_inner_smul_left, he.inner_eq_zero hnm]
  · let slabBall : Set 𝓗 := (innerSLFlip ℝ (e m)) ⁻¹' Metric.closedBall (0 : ℝ) r
    have hslabEq :
        slabBall = {x : 𝓗 | |⟪x, e m⟫_ℝ| ≤ ((2 : ℝ)⁻¹) ^ m} := by
      ext x
      simp [slabBall, innerSLFlip_apply_apply, Metric.mem_closedBall, r]
    have hbal : Balanced ℝ slabBall := by
      -- The slab is stable under contractions because the coordinate functional is linear.
      rw [balanced_iff_smul_mem]
      intro a ha x hx
      rw [hslabEq]
      have ha' : |a| ≤ 1 := by simpa [Real.norm_eq_abs] using ha
      have hx' : |⟪x, e m⟫_ℝ| ≤ r := by
        simpa [hslabEq, r] using hx
      have hr_nonneg : 0 ≤ r := by positivity
      calc
        |⟪a • x, e m⟫_ℝ| = |a| * |⟪x, e m⟫_ℝ| := by
          simp [real_inner_smul_left, abs_mul]
        _ ≤ 1 * r := by
          gcongr
        _ = r := by simp
    have hconv : Convex ℝ slabBall := by
      -- Convexity is preserved by linear preimages.
      simpa [slabBall, innerSLFlip_apply_apply, Metric.mem_closedBall, r] using
        (convex_closedBall (0 : ℝ) r).linear_preimage ((innerSLFlip ℝ (e m)).toLinearMap)
    have hAbs : AbsConvex ℝ slabBall := ⟨hbal, hconv⟩
    simpa [hslabEq, r] using hAbs
  · -- Closedness is preserved by continuous preimages.
    let slabBall : Set 𝓗 := (innerSLFlip ℝ (e m)) ⁻¹' Metric.closedBall (0 : ℝ) r
    have hslabEq :
        slabBall = {x : 𝓗 | |⟪x, e m⟫_ℝ| ≤ ((2 : ℝ)⁻¹) ^ m} := by
      ext x
      simp [slabBall, innerSLFlip_apply_apply, Metric.mem_closedBall, r]
    rw [← hslabEq]
    exact Metric.isClosed_closedBall.preimage (innerSLFlip ℝ (e m)).continuous

/-- Helper for Example 6.18: every point of the dyadic cylinder satisfies the dyadic inner-product
bound from the textbook proof. -/
lemma abs_inner_le_of_mem_dyadicSignedCylinder (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    {x : 𝓗} (hx : x ∈ dyadicSignedCylinder e) (m : ℕ) :
    |⟪x, e m⟫_ℝ| ≤ ((2 : ℝ)⁻¹) ^ m := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  let V : Submodule ℝ 𝓗 := (Submodule.span ℝ S).topologicalClosure
  rcases hx with ⟨s, hs, u, hu, rfl⟩
  have hs_slab := closedAbsConvexHull_subset_dyadic_inner_slab e he m hs
  have huV : u ∈ Vᗮ := by
    -- Replace the set-level orthogonality condition by orthogonality to the closed span.
    simpa [V, S, orthogonalSet_eq_closedSpan_orthogonal (S := S)] using hu
  have heV : e m ∈ V := by
    have hscaled : ((2 : ℝ)⁻¹ ^ m) • e m ∈ S :=
      subset_closedAbsConvexHull (by exact ⟨m, rfl⟩)
    have hspan : ((2 : ℝ)⁻¹ ^ m) • e m ∈ Submodule.span ℝ S :=
      Submodule.subset_span hscaled
    have hpow_ne : (2 : ℝ) ^ m ≠ 0 := by positivity
    have hsmul : (2 : ℝ) ^ m • (((2 : ℝ)⁻¹ ^ m) • e m) ∈ Submodule.span ℝ S :=
      (Submodule.span ℝ S).smul_mem ((2 : ℝ) ^ m) hspan
    have hmul : (2 : ℝ) ^ m * ((2 : ℝ)⁻¹ ^ m) = 1 := by
      rw [inv_pow, mul_inv_cancel₀ hpow_ne]
    have hem_span : e m ∈ Submodule.span ℝ S := by
      -- Rescale the dyadic generator back to `e m`.
      simpa [smul_smul, hmul] using hsmul
    exact (Submodule.span ℝ S).le_topologicalClosure hem_span
  have hu_zero : ⟪u, e m⟫_ℝ = 0 := by
    exact inner_eq_zero_symm.mp <| (V.mem_orthogonal u).mp huV (e m) heV
  -- The orthogonal summand contributes no coordinate in the `e m` direction.
  calc
    |⟪s + u, e m⟫_ℝ| = |⟪s, e m⟫_ℝ + ⟪u, e m⟫_ℝ| := by rw [inner_add_left]
    _ = |⟪s, e m⟫_ℝ| := by rw [hu_zero, add_zero]
    _ ≤ ((2 : ℝ)⁻¹) ^ m := hs_slab

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Helper for Example 6.18: membership in the dyadic cylinder is equivalent to membership of the
orthogonal projection onto the closed span of the base hull. -/
lemma dyadicSignedCylinder_mem_iff_starProjection_mem (e : ℕ → 𝓗) (x : 𝓗) :
    let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
    let V : Submodule ℝ 𝓗 := (Submodule.span ℝ S).topologicalClosure
    x ∈ dyadicSignedCylinder e ↔ V.starProjection x ∈ S := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  let V : Submodule ℝ 𝓗 := (Submodule.span ℝ S).topologicalClosure
  constructor
  · intro hx
    rcases hx with ⟨s, hs, u, hu, rfl⟩
    have hsV : s ∈ V :=
      (Submodule.span ℝ S).le_topologicalClosure (Submodule.subset_span hs)
    have huV : u ∈ Vᗮ := by
      simpa [V, S, orthogonalSet_eq_closedSpan_orthogonal (S := S)] using hu
    have hproj_s : V.starProjection s = s := (Submodule.starProjection_eq_self_iff).2 hsV
    have hproj_u : V.starProjection u = 0 := by
      -- A vector already in the orthogonal complement projects to `0`.
      exact Submodule.eq_starProjection_of_mem_orthogonal (K := V) (by simp) (by simpa using huV)
    -- Projection strips away exactly the orthogonal summand.
    simpa [dyadicSignedCylinder, V, S, map_add, hproj_s, hproj_u] using hs
  · intro hx
    have horth : x - V.starProjection x ∈ S^⊥ := by
      -- The projection residual lies in the orthogonal complement of the closed span.
      simpa [V, S, orthogonalSet_eq_closedSpan_orthogonal (S := S)] using
        V.sub_starProjection_mem_orthogonal x
    -- Rebuild `x` from its projection and orthogonal residual.
    refine Set.mem_add.mpr ⟨V.starProjection x, hx, x - V.starProjection x, horth, ?_⟩
    abel_nf

-- Proof sketch: let `S := closedAbsConvexHull ℝ (dyadicScaledRange e)` and
-- `V := (Submodule.span ℝ S).topologicalClosure`. The set `S` is closed by definition and lies in
-- `V`, while `S^⊥` agrees with `Vᗮ`. The Hilbert-space decomposition along the closed subspace `V`
-- identifies `dyadicSignedCylinder e = S + Vᗮ` with the preimage of `S` under the continuous
-- projection onto `V`, so the cylinder is closed.
/-- The dyadic signed cylinder is closed. -/
theorem dyadicSignedCylinder_isClosed (e : ℕ → 𝓗) :
    IsClosed (dyadicSignedCylinder e) := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  let V : Submodule ℝ 𝓗 := (Submodule.span ℝ S).topologicalClosure
  have hS_closed : IsClosed S := isClosed_closedAbsConvexHull
  -- Route correction: use the projection-preimage characterization instead of elementwise closure.
  convert hS_closed.preimage V.starProjection.continuous using 1
  ext x
  simpa [V, S] using dyadicSignedCylinder_mem_iff_starProjection_mem (e := e) x

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

-- Proof sketch: if `0` were in the interior, testing a small ball around `0` against the
-- orthonormal direction `e m` would force every interior radius to be bounded above by `2^{-m}` for
-- all `m`, which is impossible. Since the cylinder is symmetric and convex, any nonempty interior
-- would contain `0`, so the whole interior must be empty.
/-- The interior of the dyadic orthonormal cylinder is empty. -/
theorem interior_dyadicSignedCylinder_eq_empty (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) :
    interior (dyadicSignedCylinder e) = (∅ : Set 𝓗) := by
  have hC_convex : Convex ℝ (dyadicSignedCylinder e) := dyadicSignedCylinder_convex e
  have h0_not_int : (0 : 𝓗) ∉ interior (dyadicSignedCylinder e) := by
    intro h0_int
    have hmem : interior (dyadicSignedCylinder e) ∈ nhds (0 : 𝓗) :=
      isOpen_interior.mem_nhds h0_int
    rcases Metric.mem_nhds_iff.mp hmem with ⟨ε, hε_pos, hball⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ((2 : ℝ)⁻¹) ^ m < ε / 2 := by
      -- Choose a dyadic scale smaller than the interior radius.
      exact exists_pow_lt_of_lt_one (by positivity) (by norm_num : ((2 : ℝ)⁻¹) < 1)
    have hscaled_ball : (ε / 2) • e m ∈ Metric.ball (0 : 𝓗) ε := by
      -- The norm of the scaled orthonormal vector is exactly the scaling factor.
      have hhalf_lt : ε / 2 < ε := by linarith
      simpa [Metric.mem_ball, dist_eq_norm, norm_smul, he.norm_eq_one m,
        Real.norm_of_nonneg (by positivity)] using hhalf_lt
    have hscaled_mem : (ε / 2) • e m ∈ dyadicSignedCylinder e :=
      interior_subset (hball hscaled_ball)
    have hbound :=
      abs_inner_le_of_mem_dyadicSignedCylinder e he hscaled_mem m
    have habs :
        |⟪(ε / 2) • e m, e m⟫_ℝ| = ε / 2 := by
      have hhalf_pos : 0 < ε / 2 := by positivity
      have hinner : ⟪(ε / 2) • e m, e m⟫_ℝ = ε / 2 := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he.norm_eq_one m]
        ring
      rw [hinner, abs_of_pos hhalf_pos]
    have hle : ε / 2 ≤ ((2 : ℝ)⁻¹) ^ m := by
      simpa [habs] using hbound
    exact (not_lt_of_ge hle) hm
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx_mem : x ∈ dyadicSignedCylinder e := interior_subset hx
  have hx_neg : -x ∈ dyadicSignedCylinder e := by
    rw [dyadicSignedCylinder_eq_neg e, Set.mem_neg]
    simpa using hx_mem
  have hmid :
      (1 / 2 : ℝ) • (-x) + (1 / 2 : ℝ) • x ∈ interior (dyadicSignedCylinder e) := by
    -- Any nonempty interior of this symmetric convex set would force `0` into the interior.
    exact hC_convex.combo_self_interior_mem_interior hx_neg hx
      (by positivity) (by positivity) (by norm_num)
  have hzero :
      (1 / 2 : ℝ) • (-x) + (1 / 2 : ℝ) • x = (0 : 𝓗) := by
    simp [smul_neg]
  exact h0_not_int (hzero ▸ hmid)

/-- Helper for Example 6.18: the orthogonal complement of the closed span of the dyadic base hull
already lies in the dyadic signed cylinder. -/
lemma dyadicSignedCylinder_closed_span_orthogonal_subset (e : ℕ → 𝓗)
    [CompleteSpace 𝓗] :
    (((Submodule.span ℝ (closedAbsConvexHull ℝ (dyadicScaledRange e))).topologicalClosure)ᗮ :
      Set 𝓗) ⊆ dyadicSignedCylinder e := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  let V : Submodule ℝ 𝓗 := (Submodule.span ℝ S).topologicalClosure
  intro x hx
  have hzero : (0 : 𝓗) ∈ S := zero_mem_closedAbsConvexHull_dyadicScaledRange e
  have hx_orth : x ∈ S^⊥ := by
    -- Replace orthogonality to the closed span by orthogonality to the original set.
    simpa [V, S, orthogonalSet_eq_closedSpan_orthogonal (S := S)] using hx
  have hx_add : x ∈ S + S^⊥ := by
    -- Rebuild `x` as `0 + x`, with the first summand in the base hull.
    refine Set.mem_add.mpr ?_
    refine ⟨0, hzero, x, hx_orth, ?_⟩
    simp
  simpa [dyadicSignedCylinder, S] using hx_add

/-- Helper for Example 6.18: the closed linear span of the dyadic signed cylinder is the whole
Hilbert space. -/
lemma dyadicSignedCylinder_span_closure_eq_top (e : ℕ → 𝓗)
    [CompleteSpace 𝓗] :
    ((Submodule.span ℝ (dyadicSignedCylinder e)).topologicalClosure : Submodule ℝ 𝓗) = ⊤ := by
  let S : Set 𝓗 := closedAbsConvexHull ℝ (dyadicScaledRange e)
  let V : Submodule ℝ 𝓗 := (Submodule.span ℝ S).topologicalClosure
  let C : Set 𝓗 := dyadicSignedCylinder e
  let W : Submodule ℝ 𝓗 := (Submodule.span ℝ C).topologicalClosure
  have hbase_subset : S ⊆ C := by
    simpa [S, C] using dyadicSignedCylinder_base_hull_subset (e := e)
  have horth_subset : (Vᗮ : Set 𝓗) ⊆ C := by
    simpa [S, V, C] using dyadicSignedCylinder_closed_span_orthogonal_subset (e := e)
  have hV_le_W : V ≤ W := by
    -- The cylinder contains the base hull, so its closed span contains the closed span of the hull.
    have hspan : Submodule.span ℝ S ≤ Submodule.span ℝ C :=
      Submodule.span_mono hbase_subset
    exact Submodule.topologicalClosure_mono hspan
  have hVorth_le_W : Vᗮ ≤ W := by
    intro x hx
    have hxC : x ∈ C := horth_subset hx
    have hx_span : x ∈ Submodule.span ℝ C := Submodule.subset_span hxC
    exact (Submodule.span ℝ C).le_topologicalClosure hx_span
  have hsup_top : V ⊔ Vᗮ = ⊤ := by
    -- Closed subspaces of a Hilbert space admit orthogonal decomposition.
    simpa using (Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := V))
  have htop_le : ⊤ ≤ W := by
    calc
      ⊤ = V ⊔ Vᗮ := hsup_top.symm
      _ ≤ W := sup_le hV_le_W hVorth_le_W
  exact le_antisymm le_top htop_le

/-- Helper for Example 6.18: symmetry collapses the cone generated by the dyadic signed cylinder
to its linear span. -/
lemma dyadicSignedCylinder_cone_eq_span (e : ℕ → 𝓗) :
    cone (dyadicSignedCylinder e) = (Submodule.span ℝ (dyadicSignedCylinder e) : Set 𝓗) := by
  have hC_nonempty : (dyadicSignedCylinder e).Nonempty := ⟨0, zero_mem_dyadicSignedCylinder e⟩
  have hC_convex : Convex ℝ (dyadicSignedCylinder e) := dyadicSignedCylinder_convex e
  have hC_toCone :
      cone (dyadicSignedCylinder e) =
        ((hC_convex.toCone (dyadicSignedCylinder e) : ConvexCone ℝ 𝓗) : Set 𝓗) := by
    -- For a convex set, the source-facing cone agrees with the canonical positive-multiple cone.
    have hHull :
        (ConvexCone.hull ℝ (dyadicSignedCylinder e) : Set 𝓗) =
          ((hC_convex.toCone (dyadicSignedCylinder e) : ConvexCone ℝ 𝓗) : Set 𝓗) := by
      simpa [ConvexCone.hull] using
        congrArg (fun K : ConvexCone ℝ 𝓗 => (K : Set 𝓗)) hC_convex.toCone_eq_sInf.symm
    simpa [Set.cone_def] using hHull
  calc
    cone (dyadicSignedCylinder e)
        = ((hC_convex.toCone (dyadicSignedCylinder e) : ConvexCone ℝ 𝓗) : Set 𝓗) := hC_toCone
    _ = (Submodule.span ℝ (dyadicSignedCylinder e) : Set 𝓗) := by
        simpa using
          (span_eq_cone_of_eq_neg hC_nonempty hC_convex (dyadicSignedCylinder_eq_neg e)).symm

-- Proof sketch: each generator `2^{-n} e n` belongs to
-- `closedAbsConvexHull ℝ (dyadicScaledRange e)`, and balancedness supplies the opposite signs, so
-- positive scalar multiples of the orthonormal sequence lie in `cone (dyadicSignedCylinder e)`.
-- Together with the orthogonal directions already present in the cylinder, this yields a dense
-- linear span, forcing the closure of the conical hull to be all of `𝓗`.
/-- The conical closure of the dyadic orthonormal cylinder fills the whole Hilbert space. -/
theorem closure_cone_dyadicSignedCylinder_eq_univ (e : ℕ → 𝓗)
    [CompleteSpace 𝓗] (he : Orthonormal ℝ e) :
    closure (cone (dyadicSignedCylinder e)) = (univ : Set 𝓗) := by
  have _ : Orthonormal ℝ e := he
  -- Route correction: use the closed-span decomposition `V ⊔ Vᗮ = ⊤` rather than chasing the
  -- orthonormal sequence directly inside the cone.
  have hspan_top :
      ((Submodule.span ℝ (dyadicSignedCylinder e)).topologicalClosure : Submodule ℝ 𝓗) = ⊤ :=
    dyadicSignedCylinder_span_closure_eq_top (e := e)
  -- Rewrite the cone as the linear span of the symmetric cylinder, then close that submodule.
  calc
    closure (cone (dyadicSignedCylinder e))
        = closure ((Submodule.span ℝ (dyadicSignedCylinder e) : Set 𝓗)) := by
            rw [dyadicSignedCylinder_cone_eq_span (e := e)]
    _ = (((Submodule.span ℝ (dyadicSignedCylinder e)).topologicalClosure : Submodule ℝ 𝓗) :
          Set 𝓗) := by
            rw [← Submodule.topologicalClosure_coe]
    _ = (univ : Set 𝓗) := by
          rw [hspan_top]
          simp

end

end Set
