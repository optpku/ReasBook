/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

local notation "σ[" C "]" => fun u ↦ sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)

/-- Helper for Exercise 7.2: the inner-product image of a Minkowski sum is the pairwise-sum image
of the two inner-product images. -/
private lemma inner_image_add_eq_image2_add (C D : Set 𝓗) (u : 𝓗) :
    ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' (C + D)) =
      Set.image2 (· + ·) ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)
        ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D) := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, hx, rfl⟩
    rcases Set.mem_add.mp hx with ⟨c, hc, d, hd, rfl⟩
    -- Unpack membership in the Minkowski sum into a pair `(c,d)` and rewrite the inner product.
    refine Set.mem_image2.mpr ?_
    refine ⟨(⟪c, u⟫_ℝ : EReal), ⟨c, hc, rfl⟩, (⟪d, u⟫_ℝ : EReal), ⟨d, hd, rfl⟩, ?_⟩
    simp [inner_add_left]
  · intro hr
    rcases Set.mem_image2.mp hr with ⟨a, ha, b, hb, hab⟩
    rcases ha with ⟨c, hc, rfl⟩
    rcases hb with ⟨d, hd, rfl⟩
    -- Reassemble the scalar witnesses into a point of `C + D`.
    refine ⟨c + d, Set.mem_add.mpr ⟨c, hc, d, hd, rfl⟩, ?_⟩
    simpa [inner_add_left] using hab

/-- Helper for Exercise 7.2: the supremum of all pairwise sums in `EReal` is the sum of the two
individual suprema. -/
private lemma sSup_image2_add_eq (A B : Set EReal) :
    sSup (Set.image2 (· + ·) A B) = sSup A + sSup B := by
  apply le_antisymm
  · -- Every pairwise sum is bounded above by the sum of the two suprema.
    refine sSup_le ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact add_le_add (le_sSup ha) (le_sSup hb)
  · -- Approximate each supremum from below and combine the two approximants.
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases lt_sSup_iff.mp ha with ⟨a', ha', haa'⟩
    rcases lt_sSup_iff.mp hb with ⟨b', hb', hbb'⟩
    have hab' : a + b < a' + b' := EReal.add_lt_add haa' hbb'
    exact hab'.le.trans <| le_sSup <| Set.mem_image2.mpr ⟨a', ha', b', hb', rfl⟩

-- Proof sketch: evaluate both sides at `u`, expand `σ[C + D] u` and the pointwise sum
-- `σ[C] u + σ[D] u` as suprema of inner-product images, and use
-- `⟪c + d, u⟫ = ⟪c, u⟫ + ⟪d, u⟫` together with the elementary identity
-- `sup {a + b | a ∈ A, b ∈ B} = sup A + sup B` in `EReal`.
/-- Exercise 7.2: the support function of the Minkowski sum of two subsets of a real Hilbert
space is the pointwise sum of their support functions. -/
theorem supportFunction_minkowski_sum_eq_add (C D : Set 𝓗) :
    σ[C + D] = σ[C] + σ[D] := by
  -- Evaluate the function identity at an arbitrary direction `u`.
  ext u
  -- Rewrite the scalar image of `C + D` as pairwise sums of scalar images from `C` and `D`.
  rw [Pi.add_apply, inner_image_add_eq_image2_add]
  -- The supremum of these pairwise sums is the sum of the two scalar suprema.
  exact sSup_image2_add_eq _ _
