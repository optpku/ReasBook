/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Example_6_40

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

section

variable {I : Type u}

local notation "E" => lp (fun _ : I ↦ ℝ) 2

/-- Helper for Example 6.41: a vector belongs to the negative polar of the `ℓ²` positive orthant
exactly when all of its coordinates are nonpositive. -/
private theorem mem_negativePolar_positiveOrthant_iff (v : E) :
    v ∈ Set.negativePolar ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E) ↔ ∀ i, v i ≤ 0 := by
  classical
  constructor
  · intro hv i
    -- Test the polar inequality on the `i`-th standard basis vector.
    rw [Set.mem_negativePolar] at hv
    have hsingle : lp.single 2 i (1 : ℝ) ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E) := by
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [lp.single_apply, h]
    have hinner : ⟪lp.single 2 i (1 : ℝ), v⟫_ℝ ≤ 0 := hv _ hsingle
    rw [lp.inner_single_left (𝕜 := ℝ) i (1 : ℝ) v] at hinner
    change v i * 1 ≤ 0 at hinner
    simpa using hinner
  · intro hv
    -- Expand the inner product into coordinate products and sum nonpositive terms.
    rw [Set.mem_negativePolar]
    intro x hx
    rw [lp.inner_eq_tsum]
    exact tsum_nonpos fun i ↦ by
      simpa [RCLike.inner_apply, mul_comm] using
        mul_nonpos_of_nonneg_of_nonpos (hx i) (hv i)

/-- Helper for Example 6.41: once `v` lies in the negative polar of the positive orthant and is
orthogonal to `x`, the coordinatewise complementary-slackness relations follow. -/
private theorem mul_eq_zero_of_mem_negativePolar_positiveOrthant_of_mem_orthogonalSet_singleton
    {x v : E} (hx : ∀ i, 0 ≤ x i)
    (hv : v ∈ Set.negativePolar ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E))
    (horth : v ∈ Set.orthogonalSet ({x} : Set E)) :
    ∀ i, x i * v i = 0 := by
  classical
  intro i
  have hv_nonpos := (mem_negativePolar_positiveOrthant_iff (v := v)).mp hv i
  have hxv_zero : ⟪x, v⟫_ℝ = 0 := by
    -- Read the singleton orthogonality condition at the point `x`.
    rw [Set.mem_orthogonalSet] at horth
    have hx_singleton : x ∈ ({x} : Set E) := by
      simp
    exact horth x hx_singleton
  let y : E := x - (x i) • lp.single 2 i (1 : ℝ)
  have hy : y ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E) := by
    -- Zeroing the `i`-th coordinate preserves membership in the positive orthant.
    intro j
    by_cases hji : j = i
    · subst hji
      change 0 ≤ (x - (x j) • lp.single 2 j (1 : ℝ) : E) j
      change 0 ≤ x j - x j * (lp.single 2 j (1 : ℝ) : E) j
      rw [lp.single_apply]
      simp
    · have hsingle : (lp.single 2 i (1 : ℝ) : E) j = 0 := by
        rw [lp.single_apply]
        simp [hji]
      change 0 ≤ (x - (x i) • lp.single 2 i (1 : ℝ) : E) j
      change 0 ≤ x j - x i * (lp.single 2 i (1 : ℝ) : E) j
      rw [hsingle]
      simpa using hx j
  have hy_le : ⟪y, v⟫_ℝ ≤ 0 := by
    -- Apply the negative-polar inequality to the modified vector `y`.
    rw [Set.mem_negativePolar] at hv
    exact hv y hy
  have hy_eq : ⟪y, v⟫_ℝ = ⟪x, v⟫_ℝ - x i * v i := by
    -- The difference between `x` and `y` isolates the single coordinate product `x i * v i`.
    calc
      ⟪y, v⟫_ℝ = ⟪x - (x i) • lp.single 2 i (1 : ℝ), v⟫_ℝ := by
        rfl
      _ = ⟪x, v⟫_ℝ - ⟪(x i) • lp.single 2 i (1 : ℝ), v⟫_ℝ := by
        rw [inner_sub_left]
      _ = ⟪x, v⟫_ℝ - x i * ⟪lp.single 2 i (1 : ℝ), v⟫_ℝ := by
        rw [real_inner_smul_left]
      _ = ⟪x, v⟫_ℝ - x i * v i := by
        rw [lp.inner_single_left (𝕜 := ℝ) i (1 : ℝ) v]
        change ⟪x, v⟫_ℝ - x i * (v i * 1) = _
        ring
  have hnonneg : 0 ≤ x i * v i := by
    -- Since `⟪y, v⟫ ≤ 0` and `⟪x, v⟫ = 0`, the isolated term must be nonnegative.
    rw [hy_eq, hxv_zero] at hy_le
    linarith
  have hnonpos : x i * v i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hx i) hv_nonpos
  linarith

-- Proof sketch: combine the normal-cone description for convex cones from Example 6.40 with the
-- coordinatewise description of the positive and negative orthants. The orthogonality condition
-- against `x` then becomes the coordinatewise complementary-slackness equations `x i * v i = 0`.
/-- Example 6.41: at a point `x` of the positive orthant in `ℓ²(I)`, the normal cone consists
exactly of the vectors with nonpositive coordinates that satisfy the complementary-slackness
relations `x i * v i = 0` coordinatewise. -/
theorem normalCone_ell2PositiveOrthant_eq_setOf_nonpos_mul_eq_zero {x : E}
    (hx : x ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E)) :
    Set.normalCone ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E) x =
      {v : E | ∀ i, v i ≤ 0 ∧ x i * v i = 0} := by
  classical
  let K : Set E := {ξ : E | ∀ i, 0 ≤ ξ i}
  have hK_cone : IsCone K := by
    -- The positive orthant is stable under multiplication by positive scalars.
    rw [isCone_iff]
    refine subset_antisymm ?_ ?_
    · intro y hy
      have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
        simp
      have hone_smul : (1 : ℝ) • y = y := by
        simp
      exact Set.mem_smul.mpr ⟨1, hone, y, hy, hone_smul⟩
    · intro y hy
      rcases Set.mem_smul.mp hy with ⟨a, ha, z, hz, rfl⟩
      intro i
      simpa [smul_eq_mul] using mul_nonneg ha.le (hz i)
  have hK_convex : Convex ℝ K := by
    -- Coordinatewise nonnegativity is preserved by convex combinations.
    intro y hy z hz a b ha hb hab i
    simpa [K, smul_eq_mul, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc] using
      add_nonneg (mul_nonneg ha (hy i)) (mul_nonneg hb (hz i))
  have hnormal : Set.normalCone K x = K.negativePolar ∩ Set.orthogonalSet ({x} : Set E) := by
    -- Example 6.40 gives the normal cone of a convex cone as a polar/orthogonal intersection.
    exact Set.normalCone_eq_polarCone_inter_orthogonalSet_singleton_of_mem_convex_cone
      hK_cone hK_convex hx
  ext v
  constructor
  · intro hv
    -- Unpack the normal cone into polar and orthogonality conditions, then translate each one.
    rw [hnormal] at hv
    rcases hv with ⟨hv_neg, hv_orth⟩
    intro i
    constructor
    · exact (mem_negativePolar_positiveOrthant_iff (v := v)).mp hv_neg i
    · exact
        mul_eq_zero_of_mem_negativePolar_positiveOrthant_of_mem_orthogonalSet_singleton
          hx hv_neg hv_orth i
  · intro hv
    -- Rebuild the polar condition from coordinatewise nonpositivity and the orthogonality from the
    -- coordinatewise vanishing products.
    rw [hnormal]
    refine ⟨?_, ?_⟩
    · exact (mem_negativePolar_positiveOrthant_iff (v := v)).mpr fun i ↦ (hv i).1
    · rw [Set.mem_orthogonalSet]
      intro y hy
      have hyx : y = x := by
        simpa using hy
      rw [hyx]
      rw [lp.inner_eq_tsum]
      calc
        ∑' i, ⟪x i, v i⟫_ℝ = ∑' i, 0 := by
          refine tsum_congr fun i ↦ ?_
          calc
            ⟪x i, v i⟫_ℝ = v i * x i := RCLike.inner_apply (x i) (v i)
            _ = 0 := by
              simpa [mul_comm] using (hv i).2
        _ = 0 := tsum_zero

end
