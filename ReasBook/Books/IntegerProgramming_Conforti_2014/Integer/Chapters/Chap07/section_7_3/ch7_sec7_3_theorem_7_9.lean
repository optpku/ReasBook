/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_21

open scoped BigOperators

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this environment, so this file uses a direct source-faithful formalization of the
-- single-node flow set and its flow-cover inequality.

section Theorem79

variable {n : ℕ}

/-- The single-node flow set
`T = {(x,y) ∈ {0,1}^n × ℝ^n_+ | ∑ j, y_j ≤ b, y_j ≤ a_j x_j for all j}`. -/
def single_node_flow_set
    (a : Fin n → ℝ) (b : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
      (∀ j, 0 ≤ p.2 j) ∧
        (∑ j, p.2 j ≤ b) ∧
          ∀ j, p.2 j ≤ a j * p.1 j}

/-- Membership in `single_node_flow_set a b` is exactly the binary, nonnegativity, capacity, and
upper-bound system defining the single-node flow set. -/
theorem mem_single_node_flow_set_iff
    (a : Fin n → ℝ) (b : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ single_node_flow_set a b ↔
      (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
        (∀ j, 0 ≤ p.2 j) ∧
          (∑ j, p.2 j ≤ b) ∧
            ∀ j, p.2 j ≤ a j * p.1 j :=
  Iff.rfl

/-- A flow cover for the single-node flow set is a subset whose total capacity exceeds `b`. -/
class IsFlowCover
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) : Prop where
  /-- The total capacity on `C` is strictly larger than the single-node right-hand side. -/
  sum_gt_rhs : b < (∑ j ∈ C, a j)

/-- Proofs of `IsFlowCover a b C` are subsingletons because this is a proposition. -/
instance isFlowCover_subsingleton
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    Subsingleton (IsFlowCover a b C) :=
  inferInstance

/-- `IsFlowCover a b C` unfolds to the strict inequality `b < ∑ j ∈ C, a_j`. -/
theorem isFlowCover_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    IsFlowCover a b C ↔ b < (∑ j ∈ C, a j) := by
  constructor
  · intro hC
    exact hC.sum_gt_rhs
  · intro hC
    exact ⟨hC⟩

/-- A flow cover is nonempty whenever the right-hand side is nonnegative. -/
theorem flow_cover_nonempty
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hb_nonneg : 0 ≤ b)
    (hC : IsFlowCover a b C) :
    C.Nonempty := by
  by_contra hCempty
  have hEmpty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCempty
  have hlt : b < 0 := by
    simpa [hEmpty] using hC.sum_gt_rhs
  exact (not_lt_of_ge hb_nonneg) hlt

/-- The excess `λ = ∑_{j ∈ C} a_j - b` associated with the flow cover `C`. -/
def flow_cover_excess
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) : ℝ :=
  (∑ j ∈ C, a j) - b

/-- The flow-cover excess is definitionally the total cover capacity minus `b`. -/
theorem flow_cover_excess_eq_sum_sub
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    flow_cover_excess a b C = (∑ j ∈ C, a j) - b :=
  rfl

/-- A flow cover has strictly positive excess. -/
theorem flow_cover_excess_pos
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hC : IsFlowCover a b C) :
    0 < flow_cover_excess a b C := by
  rw [flow_cover_excess_eq_sum_sub]
  linarith [hC.sum_gt_rhs]

/-- The left-hand side of the flow cover inequality attached to `C` evaluated at `(x,y)`. -/
def flow_cover_value
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ j ∈ C, p.2 j) +
    ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)

/-- `flow_cover_value a b C p` expands to the explicit left-hand side of the flow cover
inequality defined by `C`. -/
theorem flow_cover_value_eq
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_value a b C p =
      (∑ j ∈ C, p.2 j) +
        ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j) :=
  rfl

/-- The equality face cut out on `conv(T)` by the flow cover inequality associated with `C`. -/
def flow_cover_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ convexHull ℝ (single_node_flow_set a b) ∧
      flow_cover_value a b C p = b}

/-- Membership in `flow_cover_face a b C` means lying in `conv(T)` and meeting the flow cover
inequality at equality. -/
theorem mem_flow_cover_face_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ flow_cover_face a b C ↔
      p ∈ convexHull ℝ (single_node_flow_set a b) ∧
        flow_cover_value a b C p = b :=
  Iff.rfl

/-- Helper for Theorem 7.9: for nonnegative capacities and positive excess `λ`, the positive-part
penalty is subadditive along two capacity contributions. -/
lemma maxSubExcess_add_le
    {u v lam : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hlam : 0 < lam) :
    max (u - lam) 0 + max (v - lam) 0 ≤ max (u + v - lam) 0 := by
  -- Split by whether each term already falls below the positive-part threshold `λ`.
  by_cases hu_le : u ≤ lam
  · by_cases hv_le : v ≤ lam
    · have hu_max : max (u - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      have hv_max : max (v - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      rw [hu_max, hv_max]
      simp
    · have hu_max : max (u - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      have hv_nonneg : 0 ≤ v - lam := by
        linarith
      have huv_nonneg : 0 ≤ u + v - lam := by
        linarith
      rw [hu_max, max_eq_left hv_nonneg, max_eq_left huv_nonneg]
      linarith
  · by_cases hv_le : v ≤ lam
    · have hv_max : max (v - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      have hu_nonneg : 0 ≤ u - lam := by
        linarith
      have huv_nonneg : 0 ≤ u + v - lam := by
        linarith
      rw [hv_max, max_eq_left hu_nonneg, max_eq_left huv_nonneg]
      linarith
    · have hu_nonneg : 0 ≤ u - lam := by
        linarith
      have hv_nonneg : 0 ≤ v - lam := by
        linarith
      have huv_nonneg : 0 ≤ u + v - lam := by
        linarith
      rw [max_eq_left hu_nonneg, max_eq_left hv_nonneg, max_eq_left huv_nonneg]
      linarith

/-- Helper for Theorem 7.9: the total positive-part penalty over a missing cover set is bounded by
the positive part of the total missing-capacity gap. -/
lemma coverPenalty_le_missingGap
    (a : Fin n → ℝ) (lam : ℝ) (M : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hlam : 0 < lam) :
    (∑ j ∈ M, max (a j - lam) 0) ≤ max ((∑ j ∈ M, a j) - lam) 0 := by
  induction M using Finset.induction_on with
  | empty =>
      -- The empty missing set contributes no penalty.
      simp
  | @insert j M hj ih =>
      have hsum_nonneg : 0 ≤ ∑ k ∈ M, a k := by
        exact Finset.sum_nonneg (fun k hk ↦ ha_nonneg k)
      -- Add the new missing item and use the two-term positive-part bound.
      calc
        ((insert j M : Finset (Fin n))).sum (fun k ↦ max (a k - lam) 0)
            = max (a j - lam) 0 + ∑ k ∈ M, max (a k - lam) 0 := by
                simp [hj]
        _ ≤ max (a j - lam) 0 + max ((∑ k ∈ M, a k) - lam) 0 := by
              gcongr
        _ ≤ max ((a j + ∑ k ∈ M, a k) - lam) 0 := by
              exact maxSubExcess_add_le (ha_nonneg j) hsum_nonneg hlam
        _ = max (((insert j M : Finset (Fin n))).sum a - lam) 0 := by
              simp [hj]

/-- Helper for Theorem 7.9: the positive-part coefficients in the canonical supporting
flow-cover functional. -/
def flowCoverSupportCoeff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) : Fin n → ℝ :=
  fun j ↦ max (a j - flow_cover_excess a b C) 0

/-- Helper for Theorem 7.9: the canonical support functional for the flow-cover inequality is
additive. -/
theorem flowCoverSupportLinearMap_map_add
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (q r : (Fin n → ℝ) × (Fin n → ℝ)) :
    (∑ j ∈ C, (q + r).2 j) -
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (q + r).1 j =
      ((∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j) +
        ((∑ j ∈ C, r.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * r.1 j) := by
  -- Expand the product-space addition and regroup the two sums.
  simp [flowCoverSupportCoeff, Finset.sum_add_distrib, sub_eq_add_neg, mul_add, add_comm,
    add_left_comm, add_assoc]

/-- Helper for Theorem 7.9: the canonical support functional for the flow-cover inequality is
homogeneous. -/
theorem flowCoverSupportLinearMap_map_smul
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (t : ℝ) (q : (Fin n → ℝ) × (Fin n → ℝ)) :
    (∑ j ∈ C, (t • q).2 j) -
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (t • q).1 j =
      t * ((∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j) := by
  -- Pull the scalar through both sums and then factor it out.
  calc
    (∑ j ∈ C, (t • q).2 j) -
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (t • q).1 j
      = (∑ j ∈ C, t * q.2 j) -
          ∑ j ∈ C, t * (flowCoverSupportCoeff a b C j * q.1 j) := by
            simp [flowCoverSupportCoeff, Pi.smul_apply, mul_left_comm]
    _ = t * (∑ j ∈ C, q.2 j) - t * ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j := by
          simp [Finset.mul_sum, sub_eq_add_neg]
    _ = t * ((∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j) := by
          ring

/-- Helper for Theorem 7.9: the canonical linear part of the flow-cover supporting hyperplane. -/
def flowCoverSupportLinearMap
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
  { toFun := fun q ↦ (∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j
    map_add' := flowCoverSupportLinearMap_map_add a b C
    map_smul' := flowCoverSupportLinearMap_map_smul a b C }

/-- Helper for Theorem 7.9: `flow_cover_value` is an affine functional whose linear part is the
cover-flow sum minus the weighted `x`-coordinates on the cover. -/
theorem flow_cover_value_eq_linear_part_add_constant
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_value a b C p =
      ((∑ j ∈ C, p.2 j) -
          ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j) +
        ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 := by
  -- Expand the penalty term into a constant part minus the weighted `x`-contribution.
  rw [flow_cover_value_eq]
  calc
    (∑ j ∈ C, p.2 j) +
        ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)
      = (∑ j ∈ C, p.2 j) +
          ((∑ j ∈ C, max (a j - flow_cover_excess a b C) 0) -
            ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j) := by
              congr 1
              calc
                ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)
                    = ∑ j ∈ C,
                        (max (a j - flow_cover_excess a b C) 0 -
                          max (a j - flow_cover_excess a b C) 0 * p.1 j) := by
                            refine Finset.sum_congr rfl ?_
                            intro j hj
                            ring
                _ = (∑ j ∈ C, max (a j - flow_cover_excess a b C) 0) -
                      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j := by
                        rw [Finset.sum_sub_distrib]
    _ =
        ((∑ j ∈ C, p.2 j) -
            ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j) +
          ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 := by
            ring

/-- Theorem 7.9 (1). Let `C` be a flow cover for the single-node flow set `T`, and let
`λ = ∑_{j ∈ C} a_j - b`. Then the flow cover inequality defined by `C` is valid for `T`. -/
theorem single_node_flow_cover_inequality_valid
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ single_node_flow_set a b) :
    flow_cover_value a b C p ≤ b := by
  rcases (mem_single_node_flow_set_iff a b p).mp hp with ⟨hx_bin, hy_nonneg, hsum, hcap⟩
  let lam : ℝ := flow_cover_excess a b C
  let M : Finset (Fin n) := C.filter (fun j ↦ p.1 j = 0)
  have hlam : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hpenalty_eq :
      ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) =
        ∑ j ∈ M, max (a j - lam) 0 := by
    -- Binary coordinates collapse the penalty to the missing-cover subset.
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rcases hx_bin j with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hweighted_eq :
      ∑ j ∈ C, a j * p.1 j = (∑ j ∈ C, a j) - ∑ j ∈ M, a j := by
    have hsplit :
        C.sum a = M.sum a + (C.filter (fun j ↦ p.1 j ≠ 0)).sum a := by
      simpa [M, add_comm, add_left_comm, add_assoc] using
        (Finset.sum_filter_add_sum_filter_not (s := C) (p := fun j ↦ p.1 j = 0) a).symm
    calc
      ∑ j ∈ C, a j * p.1 j = (C.filter (fun j ↦ p.1 j ≠ 0)).sum a := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rcases hx_bin j with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = C.sum a - M.sum a := by
        linarith
  have hflow_le_gap :
      ∑ j ∈ C, p.2 j ≤ b - max ((∑ j ∈ M, a j) - lam) 0 := by
    have hcover_bound :
        ∑ j ∈ C, p.2 j ≤ b - ((∑ j ∈ M, a j) - lam) := by
      calc
        ∑ j ∈ C, p.2 j ≤ ∑ j ∈ C, a j * p.1 j := by
          exact Finset.sum_le_sum (fun j hj ↦ hcap j)
        _ = (∑ j ∈ C, a j) - ∑ j ∈ M, a j := hweighted_eq
        _ = b - ((∑ j ∈ M, a j) - lam) := by
          dsimp [lam]
          rw [flow_cover_excess_eq_sum_sub]
          ring
    by_cases hgap_nonneg : 0 ≤ (∑ j ∈ M, a j) - lam
    · rw [max_eq_left hgap_nonneg]
      exact hcover_bound
    · rw [max_eq_right]
      · have hsum_cover : ∑ j ∈ C, p.2 j ≤ b := by
          calc
            ∑ j ∈ C, p.2 j ≤ ∑ j, p.2 j := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (by intro j hj; simp)
                (fun j _ _ ↦ hy_nonneg j)
            _ ≤ b := hsum
        simpa using hsum_cover
      · linarith
  have hpenalty_le :
      ∑ j ∈ M, max (a j - lam) 0 ≤ max ((∑ j ∈ M, a j) - lam) 0 :=
    coverPenalty_le_missingGap a lam M ha_nonneg hlam
  -- Combine the flow bound and the penalty bound on the missing-cover set.
  rw [flow_cover_value_eq, hpenalty_eq]
  linarith

/-- Since the flow-cover inequality is valid on `T`, it is also valid on `conv(T)`. -/
theorem flow_cover_value_le_of_mem_convexHull
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ convexHull ℝ (single_node_flow_set a b)) :
    flow_cover_value a b C p ≤ b := by
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let δ : ℝ := b - ∑ j ∈ C, coeff j
  let H : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | L q ≤ δ}
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hconvex : Convex ℝ H := by
    -- The valid region is a linear halfspace after separating the constant term.
    simpa [H, L] using convex_halfSpace_le L.isLinear δ
  have hsubset : single_node_flow_set a b ⊆ H := by
    intro q hq
    have hvalid :=
      single_node_flow_cover_inequality_valid a b C ha_nonneg hC hq
    have hsplit := hvalue_split q
    dsimp [H, δ]
    linarith
  have hp_mem : p ∈ H := convexHull_min hsubset hconvex hp
  have hsplit := hvalue_split p
  dsimp [H, δ] at hp_mem
  linarith

/-- Helper for Theorem 7.9: a sharp valid linear inequality identifies its equality set with the
corresponding exposed face. -/
theorem separatorEqualitySet_eq_toExposed_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {L : E →ₗ[ℝ] ℝ} {δ : ℝ} {x₀ : E}
    (hvalid : ∀ x ∈ P, L x ≤ δ)
    (hx₀P : x₀ ∈ P) (hx₀ : L x₀ = δ) :
    {x : E | x ∈ P ∧ L x = δ} =
      (⟨L, L.continuous_of_finiteDimensional⟩ : E →L[ℝ] ℝ).toExposed P := by
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    -- Equality points maximize the supporting functional because the same upper bound is valid on
    -- the whole set.
    refine ⟨hxP, ?_⟩
    intro y hyP
    calc
      L y ≤ δ := hvalid y hyP
      _ = L x := by simp [hxEq]
  · intro hx
    -- A maximizer must attain the witness value where the upper bound is already sharp.
    refine ⟨hx.1, ?_⟩
    have hx₀_le : L x₀ ≤ L x := hx.2 x₀ hx₀P
    have hx_le : L x ≤ L x₀ := by
      calc
        L x ≤ δ := hvalid x hx.1
        _ = L x₀ := hx₀.symm
    have hx_eq : L x = L x₀ := le_antisymm hx_le hx₀_le
    simpa [hx₀] using hx_eq

/-- Helper for Theorem 7.9: the standard anchor point with all cover items selected and the
anchor flow reduced by the excess lies on the flow-cover equality face. -/
theorem flow_cover_anchor_point_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    ((fun j ↦ if j ∈ C then 1 else 0),
        fun j ↦ (if j ∈ C then a j else 0) -
          if j = j0 then flow_cover_excess a b C else 0) ∈
      flow_cover_face a b C := by
  let x0 : Fin n → ℝ := fun j ↦ if j ∈ C then 1 else 0
  let y0 : Fin n → ℝ := fun j ↦
    (if j ∈ C then a j else 0) - if j = j0 then flow_cover_excess a b C else 0
  have hy0_nonneg : ∀ j, 0 ≤ y0 j := by
    intro j
    by_cases hjC : j ∈ C
    · by_cases hj0 : j = j0
      · subst hj0
        dsimp [y0]
        simp [hj0C]
        linarith
      · dsimp [y0]
        simp [hjC, hj0, ha_nonneg j]
    · have hj0_ne : j ≠ j0 := by
        intro hEq
        exact hjC (hEq.symm ▸ hj0C)
      dsimp [y0]
      simp [hjC, hj0_ne]
  have hpoint_mem : (x0, y0) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, hy0_nonneg, ?_, ?_⟩
    · -- The anchor point selects exactly the cover coordinates.
      intro j
      by_cases hjC : j ∈ C
      · simp [x0, hjC]
      · simp [x0, hjC]
    · -- The anchor flow uses exactly `b` units of total flow.
      have hsum_y :
          ∑ j, y0 j = b := by
        rw [Finset.sum_sub_distrib]
        simp [flow_cover_excess_eq_sum_sub]
      simp [hsum_y]
    · -- Each flow coordinate respects its own capacity upper bound.
      intro j
      by_cases hjC : j ∈ C
      · by_cases hj0 : j = j0
        · subst hj0
          dsimp [x0, y0]
          simp [hj0C]
          have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
          linarith
        · dsimp [x0, y0]
          simp [hjC, hj0]
      · have hj0_ne : j ≠ j0 := by
          intro hEq
          exact hjC (hEq.symm ▸ hj0C)
        dsimp [x0, y0]
        simp [hjC, hj0_ne]
  refine (mem_flow_cover_face_iff a b C (x0, y0)).2 ?_
  refine ⟨subset_convexHull ℝ _ hpoint_mem, ?_⟩
  -- On the anchor point, every cover variable is selected, so the penalty term vanishes.
  have hsum_cover :
      ∑ j ∈ C, y0 j = b := by
    simp [y0, hj0C, flow_cover_excess_eq_sum_sub]
  rw [flow_cover_value_eq]
  have hpenalty_zero :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - x0 j) = 0 := by
    -- Every cover coordinate of `x0` is `1`, so the penalty sum vanishes termwise.
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp [x0, hj]
  rw [hpenalty_zero]
  simp [hsum_cover]

/-- Helper for Theorem 7.9: once the excess is strictly smaller than one cover capacity, the
flow-cover equality set is an exposed face of `conv(T)`. -/
theorem flow_cover_face_isExposed
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    IsExposed ℝ
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C) := by
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let δ : ℝ := b - ∑ j ∈ C, coeff j
  let x0 : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hvalid :
      ∀ q ∈ convexHull ℝ (single_node_flow_set a b), L q ≤ δ := by
    intro q hq
    have hq_valid := flow_cover_value_le_of_mem_convexHull a b C ha_nonneg hC hq
    have hsplit := hvalue_split q
    dsimp [δ] at *
    linarith
  have hx0_face : x0 ∈ flow_cover_face a b C := by
    simpa [x0] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hx0_eq : L x0 = δ := by
    have hsplit := hvalue_split x0
    have hx0_level := (mem_flow_cover_face_iff a b C x0).mp hx0_face |>.2
    dsimp [δ] at *
    linarith
  have hface_eq :
      flow_cover_face a b C =
        {q | q ∈ convexHull ℝ (single_node_flow_set a b) ∧ L q = δ} := by
    ext q
    constructor
    · intro hq
      rcases (mem_flow_cover_face_iff a b C q).mp hq with ⟨hqP, hqEq⟩
      refine ⟨hqP, ?_⟩
      have hsplit := hvalue_split q
      dsimp [δ] at *
      linarith
    · intro hq
      rcases hq with ⟨hqP, hqEq⟩
      refine (mem_flow_cover_face_iff a b C q).2 ⟨hqP, ?_⟩
      have hsplit := hvalue_split q
      dsimp [δ] at *
      linarith
  have hface_toExposed :
      flow_cover_face a b C =
        (⟨L, L.continuous_of_finiteDimensional⟩ :
          ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℝ).toExposed
            (convexHull ℝ (single_node_flow_set a b)) := by
    rw [hface_eq]
    exact separatorEqualitySet_eq_toExposed_of_mem hvalid hx0_face.1 hx0_eq
  -- Rewriting the equality face as a `toExposed` set gives the canonical exposed-face fact.
  rw [hface_toExposed]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Theorem 7.9: if one cover capacity strictly exceeds the flow-cover excess, then the
single-node right-hand side `b` is positive. -/
theorem flowCover_rhs_pos
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    0 < b := by
  have hsum_split :
      C.sum a = (C.erase j0).sum a + a j0 := by
    -- Split the cover sum at the distinguished anchor index.
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
  have htail_lt : (C.erase j0).sum a < b := by
    -- Rearranging `λ < a j0` isolates the remaining cover mass below `b`.
    rw [flow_cover_excess_eq_sum_sub] at hj0lt
    rw [hsum_split] at hj0lt
    linarith
  have htail_nonneg : 0 ≤ (C.erase j0).sum a := by
    -- Nonnegative capacities force the tail cover sum to be nonnegative.
    exact Finset.sum_nonneg fun j hj ↦ ha_nonneg j
  linarith

/-- Helper for Theorem 7.9: the slack point with all items selected and zero flow lies in the
single-node flow set as soon as `b` is nonnegative. -/
theorem flowCoverLoosePoint_mem_single_node_flow_set
    (a : Fin n → ℝ) (b : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hb_nonneg : 0 ≤ b) :
    ((fun _ ↦ (1 : ℝ)), fun _ ↦ (0 : ℝ)) ∈ single_node_flow_set a b := by
  rw [mem_single_node_flow_set_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Every `x`-coordinate of the slack point equals `1`.
    intro j
    exact Or.inr rfl
  · -- The slack point has zero nonnegative flow.
    intro j
    simp
  · -- The total slack flow is zero, hence below any nonnegative right-hand side.
    simpa using hb_nonneg
  · -- Zero flow automatically satisfies every capacity upper bound.
    intro j
    simpa using ha_nonneg j

/-- Helper for Theorem 7.9: every direction of the flow-cover equality face lies in the ambient
direction and in the kernel of the supporting linear map used to expose the face. -/
theorem flowCoverFaceDirection_le_polyDirection_inf_supportKer
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    (affineSpan ℝ (flow_cover_face a b C)).direction ≤
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction ⊓ LinearMap.ker L := by
  classical
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  dsimp
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let δ : ℝ := b - ∑ j ∈ C, coeff j
  let x0 : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hx0_face : x0 ∈ flow_cover_face a b C := by
    -- Reuse the anchor point already constructed for the exposed-face proof.
    simpa [x0] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hlevel :
      ∀ q ∈ flow_cover_face a b C, L q = δ := by
    intro q hq
    have hq_eq := (mem_flow_cover_face_iff a b C q).mp hq |>.2
    have hsplit := hvalue_split q
    dsimp [δ] at *
    linarith
  have hspan_level :
      (affineSpan ℝ (flow_cover_face a b C) :
        Set ((Fin n → ℝ) × (Fin n → ℝ))) ⊆ {q | L q = δ} := by
    intro q hq
    -- The level-set condition is affine, so it extends from the face to its affine span.
    refine affineSpan_induction (k := ℝ) (s := flow_cover_face a b C)
      (p := fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ L x = δ) hq ?_ ?_
    · intro x hx
      exact hlevel x hx
    · intro t x y z hx hy hz
      simp [hx, hy, hz, sub_eq_add_neg, add_comm]
  intro v hv
  refine ⟨?_, ?_⟩
  · -- The face lives inside `conv(T)`, so its direction lies inside the ambient direction.
    simpa using
      (AffineSubspace.direction_le (affineSpan_mono ℝ (fun q hq ↦
        (mem_flow_cover_face_iff a b C q).mp hq |>.1)) hv)
  · have hx0_aff : x0 ∈ affineSpan ℝ (flow_cover_face a b C) :=
      subset_affineSpan ℝ _ hx0_face
    change L v = 0
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff] at hv
    rcases hv with ⟨x, hx_aff, rfl⟩
    -- Both endpoints lie on the same affine level set, so their difference is killed by `L`.
    have hx_eq : L x = δ := hspan_level hx_aff
    have hx0_eq : L x0 = δ := hlevel x0 hx0_face
    simp [vsub_eq_sub, hx_eq, hx0_eq]

/-- Helper for Theorem 7.9: the ambient support-kernel cut has codimension one because the
normalized difference between the anchor point and the slack point evaluates to `1`. -/
theorem flowCoverSupportKerCodimOne
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  classical
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  dsimp
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
  let x0 : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  let pLoose : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun _ ↦ (1 : ℝ)), fun _ ↦ (0 : ℝ))
  let w : (Fin n → ℝ) × (Fin n → ℝ) := b⁻¹ • (x0 - pLoose)
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hx0_face : x0 ∈ flow_cover_face a b C := by
    -- Reuse the standard exposed-face anchor point.
    simpa [x0] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hx0_mem :
      x0 ∈ convexHull ℝ (single_node_flow_set a b) :=
    (mem_flow_cover_face_iff a b C x0).mp hx0_face |>.1
  have hb_pos : 0 < b := flowCover_rhs_pos a b C ha_nonneg hj0C hj0lt
  have hpLoose_mem : pLoose ∈ single_node_flow_set a b := by
    -- The all-ones / zero-flow point is feasible because `b` is positive.
    simpa [pLoose] using
      flowCoverLoosePoint_mem_single_node_flow_set a b ha_nonneg hb_pos.le
  have hpLoose_hull :
      pLoose ∈ convexHull ℝ (single_node_flow_set a b) :=
    subset_convexHull ℝ _ hpLoose_mem
  have hx0_aff :
      x0 ∈ affineSpan ℝ (convexHull ℝ (single_node_flow_set a b)) :=
    subset_affineSpan ℝ _ hx0_mem
  have hpLoose_aff :
      pLoose ∈ affineSpan ℝ (convexHull ℝ (single_node_flow_set a b)) :=
    subset_affineSpan ℝ _ hpLoose_hull
  have hdiff_mem :
      x0 - pLoose ∈ D := by
    -- Differences of two ambient points lie in the ambient direction.
    rw [show D = (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction by rfl]
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hpLoose_aff]
    refine ⟨x0, hx0_aff, ?_⟩
    simp [vsub_eq_sub]
  have hwD : w ∈ D := by
    -- Scaling a direction vector keeps it inside the ambient direction.
    simpa [w] using D.smul_mem (b⁻¹) hdiff_mem
  have hx0_eval :
      L x0 = b - ∑ j ∈ C, coeff j := by
    -- The anchor point lies on the equality face, so the supporting functional hits `δ`.
    have hx0_eq := (mem_flow_cover_face_iff a b C x0).mp hx0_face |>.2
    have hsplit := hvalue_split x0
    linarith
  have hpLoose_eval :
      L pLoose = -∑ j ∈ C, coeff j := by
    -- The slack point has zero flow and all cover selectors equal to one.
    simp [L, coeff, pLoose, flowCoverSupportLinearMap, flowCoverSupportCoeff]
  have hw_eval : L w = 1 := by
    -- Normalizing the anchor-slack difference divides its `L`-value `b` down to `1`.
    have hdiff_eval : L (x0 - pLoose) = b := by
      calc
        L (x0 - pLoose) = L x0 - L pLoose := by
          simp [LinearMap.map_sub]
        _ = b := by
          linarith [hx0_eval, hpLoose_eval]
    calc
      L w = b⁻¹ * L (x0 - pLoose) := by
        simp [w]
      _ = b⁻¹ * b := by rw [hdiff_eval]
      _ = 1 := by
        field_simp [hb_pos.ne']
  exact submodule_finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval

/-- Helper for Theorem 7.9: if a capacity coordinate is zero, then every ambient direction vector
has zero `y`-component on that coordinate. -/
theorem singleNodeFlowAmbientDirection_y_zero_of_capacity_zero
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j)
    {i : Fin n} {v : (Fin n → ℝ) × (Fin n → ℝ)}
    (hv :
      v ∈ (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction)
    (hai : a i = 0) :
    v.2 i = 0 := by
  classical
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  let x0 : Fin n → ℝ := fun j ↦ if j ∈ C then 1 else 0
  let y0 : Fin n → ℝ := fun j ↦
    (if j ∈ C then a j else 0) - if j = j0 then flow_cover_excess a b C else 0
  let p0 : (Fin n → ℝ) × (Fin n → ℝ) := (x0, y0)
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) := convexHull ℝ (single_node_flow_set a b)
  have hp0_face : p0 ∈ flow_cover_face a b C := by
    -- Reuse the standard anchor point on the equality face.
    simpa [p0, x0, y0] using
      flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hp0_aff : p0 ∈ affineSpan ℝ P := by
    -- The anchor point lies in the ambient affine span because it lies in the face.
    exact subset_affineSpan ℝ _ ((mem_flow_cover_face_iff a b C p0).mp hp0_face).1
  have hp0_zero : p0.2 i = 0 := by
    -- The anchor point has zero `y_i` whenever the capacity itself is zero.
    by_cases hiC : i ∈ C
    · have hij0 : i ≠ j0 := by
        intro hij0
        subst hij0
        rw [hai] at hj0lt
        have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
        linarith
      simp [p0, y0, hiC, hij0, hai]
    · have hij0 : i ≠ j0 := by
        intro hij0
        exact hiC (hij0.symm ▸ hj0C)
      simp [p0, y0, hiC, hij0]
  let H : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | q.2 i = 0}
  have hH_convex : Convex ℝ H := by
    -- The zero-coordinate slice is a convex set.
    intro x hx y hy t s ht hs hts
    dsimp [H] at hx hy ⊢
    simp [hx, hy]
  have hsubset_H : single_node_flow_set a b ⊆ H := by
    intro q hq
    rcases (mem_single_node_flow_set_iff a b q).mp hq with ⟨_, hy_nonneg, _, hcap⟩
    dsimp [H]
    have hqi_nonneg : 0 ≤ q.2 i := hy_nonneg i
    have hqi_le : q.2 i ≤ a i * q.1 i := hcap i
    rw [hai] at hqi_le
    linarith
  have hcoord_zero :
      ∀ q ∈ affineSpan ℝ P, q.2 i = 0 := by
    intro q hq
    -- First extend the coordinate-zero property from `T` to `conv(T)`, then to its affine span.
    refine affineSpan_induction (k := ℝ) (s := P)
      (p := fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ x.2 i = 0) hq ?_ ?_
    · intro x hx
      exact (convexHull_min hsubset_H hH_convex hx : x ∈ H)
    · intro t x y z hx hy hz
      simp [hx, hy, hz, sub_eq_add_neg, add_comm]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hp0_aff] at hv
  rcases hv with ⟨x, hx_aff, rfl⟩
  -- Subtracting two ambient points with the same zero `y_i` coordinate keeps that coordinate zero.
  have hx_zero : x.2 i = 0 := hcoord_zero x hx_aff
  simp [vsub_eq_sub, hx_zero, hp0_zero]

/-- Helper for Theorem 7.9: for positive excess, the canonical support coefficient is the
capacity minus the exchanged amount `min (a_j) λ`. -/
theorem flowCoverSupportCoeff_eq_sub_min
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hC : IsFlowCover a b C)
    (j : Fin n) :
    flowCoverSupportCoeff a b C j =
      a j - min (a j) (flow_cover_excess a b C) := by
  have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
  by_cases hle : flow_cover_excess a b C ≤ a j
  · -- When the excess fits inside `a j`, the coefficient is the remaining slack `a j - λ`.
    rw [flowCoverSupportCoeff, min_eq_right hle, max_eq_left (by linarith)]
  · have hlt : a j < flow_cover_excess a b C := by linarith
    -- When `a j < λ`, the coefficient vanishes and so does `a j - min (a j) λ`.
    rw [flowCoverSupportCoeff, min_eq_left hlt.le, max_eq_right]
    · ring
    · linarith

/-- Helper for Theorem 7.9: when the distinguished anchor `j0 ∈ C` satisfies
`flow_cover_excess a b C < a j0`, its support coefficient is exactly `a j0 - λ`. -/
theorem flowCoverSupportCoeff_anchor_eq
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hC : IsFlowCover a b C)
    {j0 : Fin n}
    (hj0lt : flow_cover_excess a b C < a j0) :
    flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
  -- The anchor index lies in the positive-part regime because `λ < a j0`.
  rw [flowCoverSupportCoeff_eq_sub_min a b C hC j0, min_eq_right hj0lt.le]

/-- Helper for Theorem 7.9: deleting an anchor `j0` with `flow_cover_excess a b C < a j0`
leaves the remaining cover capacity strictly below `b`. -/
theorem flowCoverEraseSum_lt_rhs
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    (C.erase j0).sum a < b := by
  have hsum_split :
      C.sum a = (C.erase j0).sum a + a j0 := by
    -- Split the cover sum into the dropped tail and the distinguished anchor term.
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
  -- Rearranging `λ < a j0` isolates the remaining cover mass below the right-hand side.
  rw [flow_cover_excess_eq_sum_sub] at hj0lt
  rw [hsum_split] at hj0lt
  linarith

/-- Helper for Theorem 7.9: on the dropped-anchor witness, the cover-flow sum over `C` is exactly
the erased cover sum. -/
theorem flowCoverDroppedAnchorCoverSum_eq
    (a : Fin n → ℝ) (C : Finset (Fin n))
    {j0 : Fin n}
    (hj0C : j0 ∈ C) :
    (∑ j ∈ C, (if j ∈ C.erase j0 then a j else 0 : ℝ)) = (C.erase j0).sum a := by
  -- Rewrite the cover-restricted witness so the dropped anchor is the only omitted term.
  have hrewrite :
      (∑ j ∈ C, (if j ∈ C.erase j0 then a j else 0 : ℝ)) =
        ∑ j ∈ C, (if j = j0 then 0 else a j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hji : j = j0
    · subst hji
      simp
    · have hjErase : j ∈ C.erase j0 := by
        simp [Finset.mem_erase, hji, hj]
      simp [hjErase, hji]
  rw [hrewrite]
  calc
    ∑ j ∈ C, (if j = j0 then 0 else a j)
        = Finset.sum (C.erase j0) (fun j ↦ if j = j0 then 0 else a j) +
            (if j0 = j0 then 0 else a j0) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_erase_add
                  (s := C)
                  (f := fun j ↦ if j = j0 then 0 else a j)
                  hj0C).symm
    _ = (C.erase j0).sum a := by
      have hsum :
          Finset.sum (C.erase j0) (fun j ↦ if j = j0 then 0 else a j) =
            (C.erase j0).sum a := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hji : j ≠ j0 := (Finset.mem_erase.mp hj).1
        simp [hji]
      simpa using hsum

/-- Helper for Theorem 7.9: on the dropped-anchor witness, the penalty sum over `C` reduces to the
unique surviving anchor coefficient. -/
theorem flowCoverDroppedAnchorPenalty_eq_singleton
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {j0 : Fin n}
    (hj0C : j0 ∈ C) :
    (∑ j ∈ C,
        flowCoverSupportCoeff a b C j *
          (1 - (if j ∈ C.erase j0 then (1 : ℝ) else 0))) =
      flowCoverSupportCoeff a b C j0 := by
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  have hsplit :
      (∑ j ∈ C, coeff j * (1 - (if j ∈ C.erase j0 then (1 : ℝ) else 0))) =
        (∑ j ∈ C.erase j0, coeff j * (1 - (if j ∈ C.erase j0 then (1 : ℝ) else 0))) +
          coeff j0 * (1 - (if j0 ∈ C.erase j0 then (1 : ℝ) else 0)) := by
    -- Split the penalty sum at the anchor coordinate.
    simpa [coeff, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add
        (s := C)
        (f := fun j ↦ coeff j * (1 - (if j ∈ C.erase j0 then (1 : ℝ) else 0)))
        hj0C).symm
  have htail_zero :
      ∑ j ∈ C.erase j0, coeff j * (1 - (if j ∈ C.erase j0 then (1 : ℝ) else 0)) = 0 := by
    -- Every erased-cover term has selector `1`, so its penalty contribution vanishes.
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp [coeff, hj]
  rw [hsplit, htail_zero]
  simp [coeff]

/-- Helper for Theorem 7.9: dropping the distinguished cover item leaves a feasible point on the
flow-cover equality face, with the missing penalty carried entirely by that anchor. -/
theorem flowCoverDroppedAnchorPoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    ((fun j ↦ if j ∈ C.erase j0 then 1 else 0),
        fun j ↦ if j ∈ C.erase j0 then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let xDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then 1 else 0
  let yDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then a j else 0
  have htail_lt : (C.erase j0).sum a < b :=
    flowCoverEraseSum_lt_rhs a b C hj0C hj0lt
  have hpoint_mem : (xDrop, yDrop) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The dropped selector is still binary coordinatewise.
      intro j
      by_cases hj : j ∈ C.erase j0
      · right
        simp only [xDrop, if_pos hj]
      · left
        simp only [xDrop, if_neg hj]
    · -- Each retained flow is a nonnegative capacity, and all other flows vanish.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp only [yDrop, if_pos hj]
        exact ha_nonneg j
      · simp only [yDrop, if_neg hj]
        exact le_rfl
    · -- The total retained capacity is strictly below `b`.
      have hsum_drop : ∑ j, yDrop j = (C.erase j0).sum a := by
        calc
          ∑ j, yDrop j = ∑ j ∈ C.erase j0, yDrop j := by
            symm
            refine Finset.sum_subset (Finset.subset_univ _) ?_
            intro j hjUniv hj
            simp only [yDrop, if_neg hj]
          _ = (C.erase j0).sum a := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp only [yDrop, if_pos hj]
      rw [hsum_drop]
      exact htail_lt.le
    · -- Retained coordinates saturate their selected capacity bounds.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp only [xDrop, yDrop, if_pos hj, mul_one]
        exact le_refl (a j)
      · simp only [xDrop, yDrop, if_neg hj, mul_zero]
        exact le_refl (0 : ℝ)
  refine (mem_flow_cover_face_iff a b C (xDrop, yDrop)).2 ⟨?_, ?_⟩
  · exact subset_convexHull ℝ _ hpoint_mem
  · have hcover_sum : ∑ j ∈ C, yDrop j = (C.erase j0).sum a := by
      simpa [yDrop] using flowCoverDroppedAnchorCoverSum_eq a C hj0C
    have hpenalty :
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (1 - xDrop j) =
          flowCoverSupportCoeff a b C j0 := by
      simpa [xDrop] using flowCoverDroppedAnchorPenalty_eq_singleton a b C hj0C
    have hcoeff_anchor :
        flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C :=
      flowCoverSupportCoeff_anchor_eq a b C hC hj0lt
    have hsum_split : C.sum a = (C.erase j0).sum a + a j0 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
    have hbalance : (C.erase j0).sum a + flowCoverSupportCoeff a b C j0 = b := by
      rw [hcoeff_anchor, flow_cover_excess_eq_sum_sub, hsum_split]
      ring
    -- The retained cover flow and the unique anchor penalty add back to `b`.
    rw [flow_cover_value_eq]
    change (∑ j ∈ C, yDrop j) +
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (1 - xDrop j) = b
    rw [hcover_sum, hpenalty, hbalance]

/-- Helper for Theorem 7.9: `flow_cover_value` only depends on the coordinates indexed by the
cover `C`. -/
theorem flowCoverValue_eq_of_coverCoordinateAgreement
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {p q : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : ∀ j ∈ C, p.1 j = q.1 j)
    (hy : ∀ j ∈ C, p.2 j = q.2 j) :
    flow_cover_value a b C p = flow_cover_value a b C q := by
  have hsum_y : ∑ j ∈ C, p.2 j = ∑ j ∈ C, q.2 j :=
    Finset.sum_congr rfl (fun j hj ↦ hy j hj)
  have hsum_x :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j) =
        ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - q.1 j) :=
    Finset.sum_congr rfl (fun j hj ↦ by rw [hx j hj])
  -- Both sums in the face functional only inspect cover coordinates.
  rw [flow_cover_value_eq, flow_cover_value_eq, hsum_y, hsum_x]

/-- Helper for Theorem 7.9: toggling an outside selector on top of the dropped-anchor point keeps
the point on the same equality face because outside coordinates do not enter the face equation. -/
theorem flowCoverOutsideTogglePoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
        fun j ↦ if j ∈ C.erase j0 then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let xToggle : Fin n → ℝ :=
    fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0
  let yDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then a j else 0
  let xDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then 1 else 0
  have htail_lt : (C.erase j0).sum a < b :=
    flowCoverEraseSum_lt_rhs a b C hj0C hj0lt
  have hpoint_mem : (xToggle, yDrop) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Toggling one outside coordinate preserves binary selectors.
      intro j
      by_cases hji : j = i
      · right
        simp only [xToggle, if_pos hji]
      · by_cases hj : j ∈ C.erase j0
        · right
          simp only [xToggle, if_neg hji, if_pos hj]
        · left
          simp only [xToggle, if_neg hji, if_neg hj]
    · -- The flow vector is unchanged from the dropped-anchor witness.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp only [yDrop, if_pos hj]
        exact ha_nonneg j
      · simp only [yDrop, if_neg hj]
        exact le_rfl
    · have hsum_drop : ∑ j, yDrop j = (C.erase j0).sum a := by
        calc
          ∑ j, yDrop j = ∑ j ∈ C.erase j0, yDrop j := by
            symm
            refine Finset.sum_subset (Finset.subset_univ _) ?_
            intro j hjUniv hj
            simp only [yDrop, if_neg hj]
          _ = (C.erase j0).sum a := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp only [yDrop, if_pos hj]
      rw [hsum_drop]
      exact htail_lt.le
    · intro j
      by_cases hji : j = i
      · subst j
        have hiErase : i ∉ C.erase j0 := by
          intro hi
          exact hiC (Finset.mem_erase.mp hi).2
        simp only [xToggle, yDrop, if_pos rfl, if_neg hiErase]
        simpa using ha_nonneg i
      · by_cases hj : j ∈ C.erase j0
        · simp only [xToggle, yDrop, if_neg hji, if_pos hj, mul_one]
          exact le_refl (a j)
        · simp only [xToggle, yDrop, if_neg hji, if_neg hj, mul_zero]
          exact le_refl (0 : ℝ)
  refine (mem_flow_cover_face_iff a b C (xToggle, yDrop)).2 ⟨?_, ?_⟩
  · exact subset_convexHull ℝ _ hpoint_mem
  · have hpDrop : (xDrop, yDrop) ∈ flow_cover_face a b C := by
      simpa [xDrop, yDrop] using
        flowCoverDroppedAnchorPoint_mem_face a b C ha_nonneg hC hj0C hj0lt
    have hx : ∀ j ∈ C, xToggle j = xDrop j := by
      intro j hjC
      have hji : j ≠ i := by
        intro hEq
        exact hiC (hEq.symm ▸ hjC)
      simp [xToggle, xDrop, hji]
    have hy : ∀ j ∈ C, yDrop j = yDrop j := by
      intro j hjC
      rfl
    -- Outside selectors do not occur in the supporting functional.
    calc
      flow_cover_value a b C (xToggle, yDrop) =
          flow_cover_value a b C (xDrop, yDrop) :=
        flowCoverValue_eq_of_coverCoordinateAgreement a b C hx hy
      _ = b := (mem_flow_cover_face_iff a b C (xDrop, yDrop)).mp hpDrop |>.2

/-- Helper for Theorem 7.9: the outside-flow witness adds as much outside flow as the dropped
anchor slack allows, while remaining on the same equality face. -/
theorem flowCoverOutsideFlowPoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
        fun j ↦ if j ∈ C.erase j0 then a j
          else if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0) ∈
      flow_cover_face a b C := by
  classical
  let coeff0 : ℝ := flowCoverSupportCoeff a b C j0
  let m : ℝ := min (a i) coeff0
  let xToggle : Fin n → ℝ :=
    fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0
  let yFlow : Fin n → ℝ :=
    fun j ↦ if j ∈ C.erase j0 then a j else if j = i then m else 0
  let xDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then 1 else 0
  let yDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then a j else 0
  have hcoeff0_eq : coeff0 = a j0 - flow_cover_excess a b C :=
    flowCoverSupportCoeff_anchor_eq a b C hC hj0lt
  have hcoeff0_pos : 0 < coeff0 := by
    rw [hcoeff0_eq]
    linarith
  have hm_nonneg : 0 ≤ m := by
    exact le_min (ha_nonneg i) hcoeff0_pos.le
  have hbalance : (C.erase j0).sum a + coeff0 = b := by
    have hsum_split : C.sum a = (C.erase j0).sum a + a j0 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
    rw [hcoeff0_eq, flow_cover_excess_eq_sum_sub, hsum_split]
    ring
  have hsum_flow : ∑ j, yFlow j = (C.erase j0).sum a + m := by
    have hiErase : i ∉ C.erase j0 := by
      intro hi
      exact hiC (Finset.mem_erase.mp hi).2
    calc
      ∑ j, yFlow j =
          ∑ j, ((if j ∈ C.erase j0 then a j else 0) +
            (if j = i then m else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hjErase : j ∈ C.erase j0
              · have hji : j ≠ i := by
                  intro hEq
                  exact hiErase (hEq ▸ hjErase)
                simp only [yFlow, if_pos hjErase, if_neg hji]
                ring
              · simp only [yFlow, if_neg hjErase, zero_add]
      _ = (∑ j, if j ∈ C.erase j0 then a j else 0) +
          ∑ j, if j = i then m else 0 := Finset.sum_add_distrib
      _ = (C.erase j0).sum a + m := by
        have hfirst : ∑ j, (if j ∈ C.erase j0 then a j else 0) =
            (C.erase j0).sum a := by
          calc
            ∑ j, (if j ∈ C.erase j0 then a j else 0) =
                ∑ j ∈ C.erase j0, (if j ∈ C.erase j0 then a j else 0) := by
              symm
              refine Finset.sum_subset (Finset.subset_univ _) ?_
              intro j hjUniv hj
              rw [if_neg hj]
            _ = (C.erase j0).sum a := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [if_pos hj]
        rw [hfirst]
        simp
  have hpoint_mem : (xToggle, yFlow) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · right
        simp only [xToggle, if_pos hji]
      · by_cases hj : j ∈ C.erase j0
        · right
          simp only [xToggle, if_neg hji, if_pos hj]
        · left
          simp only [xToggle, if_neg hji, if_neg hj]
    · intro j
      by_cases hj : j ∈ C.erase j0
      · simp only [yFlow, if_pos hj]
        exact ha_nonneg j
      · by_cases hji : j = i
        · simp only [yFlow, if_neg hj, if_pos hji]
          exact hm_nonneg
        · simp only [yFlow, if_neg hj, if_neg hji]
          exact le_rfl
    · rw [hsum_flow]
      calc
        (C.erase j0).sum a + m ≤ (C.erase j0).sum a + coeff0 := by
          exact add_le_add_right (min_le_right (a i) coeff0) _
        _ = b := hbalance
    · intro j
      by_cases hj : j ∈ C.erase j0
      · have hji : j ≠ i := by
          intro hEq
          exact hiC (hEq.symm ▸ (Finset.mem_erase.mp hj).2)
        simp only [xToggle, yFlow, if_neg hji, if_pos hj, mul_one]
        exact le_refl (a j)
      · by_cases hji : j = i
        · subst j
          simp only [xToggle, yFlow, if_pos rfl, if_neg hj, if_true, mul_one]
          simpa only [m] using min_le_left (a i) coeff0
        · simp only [xToggle, yFlow, if_neg hji, if_neg hj, mul_zero]
          exact le_refl (0 : ℝ)
  refine (mem_flow_cover_face_iff a b C (xToggle, yFlow)).2 ⟨?_, ?_⟩
  · exact subset_convexHull ℝ _ hpoint_mem
  · have hpDrop : (xDrop, yDrop) ∈ flow_cover_face a b C := by
      simpa [xDrop, yDrop] using
        flowCoverDroppedAnchorPoint_mem_face a b C ha_nonneg hC hj0C hj0lt
    have hx : ∀ j ∈ C, xToggle j = xDrop j := by
      intro j hjC
      have hji : j ≠ i := by
        intro hEq
        exact hiC (hEq.symm ▸ hjC)
      simp [xToggle, xDrop, hji]
    have hy : ∀ j ∈ C, yFlow j = yDrop j := by
      intro j hjC
      have hji : j ≠ i := by
        intro hEq
        exact hiC (hEq.symm ▸ hjC)
      simp [yFlow, yDrop, hji]
    -- The added flow is also outside `C`, so the face value is unchanged.
    calc
      flow_cover_value a b C (xToggle, yFlow) =
          flow_cover_value a b C (xDrop, yDrop) :=
        flowCoverValue_eq_of_coverCoordinateAgreement a b C hx hy
      _ = b := (mem_flow_cover_face_iff a b C (xDrop, yDrop)).mp hpDrop |>.2

/-- Helper for Theorem 7.9: exchanging `min (a_i) λ` units of cover flow from `i` to the anchor
keeps the point on the same equality face. -/
theorem flowCoverCoverExchangePoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun j ↦ if j ∈ C then 1 else 0),
        fun j ↦
          if j = j0 then flowCoverSupportCoeff a b C j0 +
              min (a i) (flow_cover_excess a b C)
          else if j = i then a i - min (a i) (flow_cover_excess a b C)
          else if j ∈ C then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let lam : ℝ := flow_cover_excess a b C
  let m : ℝ := min (a i) lam
  let coeff0 : ℝ := flowCoverSupportCoeff a b C j0
  let xCover : Fin n → ℝ := fun j ↦ if j ∈ C then 1 else 0
  let yAnchor : Fin n → ℝ :=
    fun j ↦ (if j ∈ C then a j else 0) - if j = j0 then lam else 0
  let yExchange : Fin n → ℝ := fun j ↦
    if j = j0 then coeff0 + m
    else if j = i then a i - m
    else if j ∈ C then a j else 0
  have hi_mem := Finset.mem_erase.mp hi
  have hij0 : i ≠ j0 := hi_mem.1
  have hiC : i ∈ C := hi_mem.2
  have hcoeff0_eq : coeff0 = a j0 - lam := by
    simpa only [coeff0, lam] using
      flowCoverSupportCoeff_anchor_eq a b C hC hj0lt
  have hlam_pos : 0 < lam := by
    simpa only [lam] using flow_cover_excess_pos a b C hC
  have hm_nonneg : 0 ≤ m := le_min (ha_nonneg i) hlam_pos.le
  have hy_decomp :
      yExchange = fun j ↦ yAnchor j + (if j = j0 then m else 0) -
        if j = i then m else 0 := by
    funext j
    by_cases hj0 : j = j0
    · subst j
      simp only [yExchange, yAnchor, if_pos rfl, if_pos hj0C, if_neg hij0.symm,
        if_true, sub_zero]
      rw [hcoeff0_eq]
    · by_cases hji : j = i
      · subst j
        simp only [yExchange, yAnchor, if_neg hij0, if_pos hiC, if_true]
        ring
      · by_cases hjC : j ∈ C
        · simp only [yExchange, yAnchor, if_neg hj0, if_neg hji, if_pos hjC]
          ring
        · simp only [yExchange, yAnchor, if_neg hj0, if_neg hji, if_neg hjC]
          ring
  have hsum_anchor : ∑ j, yAnchor j = b := by
    simp [yAnchor, lam, flow_cover_excess_eq_sum_sub]
  have hsum_exchange : ∑ j, yExchange j = b := by
    rw [hy_decomp, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum_anchor]
    simp
  have hpoint_mem : (xCover, yExchange) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Every selector is the cover indicator.
      intro j
      by_cases hjC : j ∈ C
      · right
        simp only [xCover, if_pos hjC]
      · left
        simp only [xCover, if_neg hjC]
    · -- The exchanged flow stays nonnegative at both modified coordinates.
      intro j
      by_cases hj0 : j = j0
      · subst j
        simp only [yExchange, if_pos rfl]
        linarith
      · by_cases hji : j = i
        · subst j
          simp only [yExchange, if_neg hij0, if_true]
          exact sub_nonneg.mpr (min_le_left (a i) lam)
        · by_cases hjC : j ∈ C
          · simp only [yExchange, if_neg hj0, if_neg hji, if_pos hjC]
            exact ha_nonneg j
          · simp only [yExchange, if_neg hj0, if_neg hji, if_neg hjC]
            exact le_refl (0 : ℝ)
    · rw [hsum_exchange]
    · -- The transferred amount is bounded by the released flow and by the anchor slack.
      intro j
      by_cases hj0 : j = j0
      · subst j
        simp only [xCover, yExchange, if_pos rfl, if_pos hj0C, mul_one]
        rw [hcoeff0_eq]
        linarith [min_le_right (a i) lam]
      · by_cases hji : j = i
        · subst j
          simp only [xCover, yExchange, if_neg hij0, if_pos hiC, if_true,
            mul_one]
          linarith [min_le_left (a i) lam]
        · by_cases hjC : j ∈ C
          · simp only [xCover, yExchange, if_neg hj0, if_neg hji, if_pos hjC, mul_one]
            exact le_refl (a j)
          · simp only [xCover, yExchange, if_neg hj0, if_neg hji, if_neg hjC, mul_zero]
            exact le_refl (0 : ℝ)
  refine (mem_flow_cover_face_iff a b C (xCover, yExchange)).2 ⟨?_, ?_⟩
  · exact subset_convexHull ℝ _ hpoint_mem
  · have hsupport : ∀ j ∈ Finset.univ, j ∉ C → yExchange j = 0 := by
      intro j hjUniv hjC
      have hj0 : j ≠ j0 := by
        intro hEq
        exact hjC (hEq ▸ hj0C)
      have hji : j ≠ i := by
        intro hEq
        exact hjC (hEq ▸ hiC)
      simp only [yExchange, if_neg hj0, if_neg hji, if_neg hjC]
    have hcover_sum : ∑ j ∈ C, yExchange j = b := by
      calc
        ∑ j ∈ C, yExchange j = ∑ j, yExchange j :=
          Finset.sum_subset (Finset.subset_univ C) hsupport
        _ = b := hsum_exchange
    have hpenalty_zero :
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (1 - xCover j) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hjC
      simp only [xCover, if_pos hjC, sub_self, mul_zero]
    -- All cover selectors remain selected, so only the conserved cover-flow sum remains.
    rw [flow_cover_value_eq]
    change (∑ j ∈ C, yExchange j) +
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (1 - xCover j) = b
    rw [hcover_sum, hpenalty_zero, add_zero]

/-- Helper for Theorem 7.9: dropping a cover selector while moving `min (a_i) λ` units of flow
to the anchor stays on the same flow-cover equality face. -/
theorem flowCoverCoverDropPoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun j ↦ if j = i then 0 else if j ∈ C then 1 else 0),
        fun j ↦
          if j = j0 then flowCoverSupportCoeff a b C j0 +
              min (a i) (flow_cover_excess a b C)
          else if j = i then 0
          else if j ∈ C then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let lam : ℝ := flow_cover_excess a b C
  let m : ℝ := min (a i) lam
  let coeff0 : ℝ := flowCoverSupportCoeff a b C j0
  let coeffi : ℝ := flowCoverSupportCoeff a b C i
  let xDrop : Fin n → ℝ := fun j ↦ if j = i then 0 else if j ∈ C then 1 else 0
  let yAnchor : Fin n → ℝ :=
    fun j ↦ (if j ∈ C then a j else 0) - if j = j0 then lam else 0
  let yDrop : Fin n → ℝ := fun j ↦
    if j = j0 then coeff0 + m
    else if j = i then 0
    else if j ∈ C then a j else 0
  have hi_mem := Finset.mem_erase.mp hi
  have hij0 : i ≠ j0 := hi_mem.1
  have hiC : i ∈ C := hi_mem.2
  have hcoeff0_eq : coeff0 = a j0 - lam := by
    simpa only [coeff0, lam] using
      flowCoverSupportCoeff_anchor_eq a b C hC hj0lt
  have hcoeffi_eq : coeffi = a i - m := by
    simpa only [coeffi, m, lam] using
      flowCoverSupportCoeff_eq_sub_min a b C hC i
  have hlam_pos : 0 < lam := by
    simpa only [lam] using flow_cover_excess_pos a b C hC
  have hm_nonneg : 0 ≤ m := le_min (ha_nonneg i) hlam_pos.le
  have hcoeffi_nonneg : 0 ≤ coeffi := by
    rw [hcoeffi_eq]
    exact sub_nonneg.mpr (min_le_left (a i) lam)
  have hy_decomp :
      yDrop = fun j ↦ yAnchor j + (if j = j0 then m else 0) -
        if j = i then a i else 0 := by
    funext j
    by_cases hj0 : j = j0
    · subst j
      simp only [yDrop, yAnchor, if_pos rfl, if_pos hj0C, if_neg hij0.symm,
        if_true, sub_zero]
      rw [hcoeff0_eq]
    · by_cases hji : j = i
      · subst j
        simp only [yDrop, yAnchor, if_neg hij0, if_pos hiC, if_true]
        ring
      · by_cases hjC : j ∈ C
        · simp only [yDrop, yAnchor, if_neg hj0, if_neg hji, if_pos hjC]
          ring
        · simp only [yDrop, yAnchor, if_neg hj0, if_neg hji, if_neg hjC]
          ring
  have hsum_anchor : ∑ j, yAnchor j = b := by
    simp [yAnchor, lam, flow_cover_excess_eq_sum_sub]
  have hsum_drop : ∑ j, yDrop j = b - coeffi := by
    rw [hy_decomp, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum_anchor]
    simp
    rw [hcoeffi_eq]
    ring
  have hpoint_mem : (xDrop, yDrop) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The selected cover indicator is changed only by setting `x_i` to zero.
      intro j
      by_cases hji : j = i
      · left
        simp only [xDrop, if_pos hji]
      · by_cases hjC : j ∈ C
        · right
          simp only [xDrop, if_neg hji, if_pos hjC]
        · left
          simp only [xDrop, if_neg hji, if_neg hjC]
    · -- The dropped coordinate is zero; the other flow coordinates remain nonnegative.
      intro j
      by_cases hj0 : j = j0
      · subst j
        simp only [yDrop, if_pos rfl]
        linarith
      · by_cases hji : j = i
        · subst j
          simp only [yDrop, if_neg hij0, if_true, le_refl]
        · by_cases hjC : j ∈ C
          · simp only [yDrop, if_neg hj0, if_neg hji, if_pos hjC]
            exact ha_nonneg j
          · simp only [yDrop, if_neg hj0, if_neg hji, if_neg hjC, le_refl]
    · rw [hsum_drop]
      linarith
    · -- The anchor transfer fits its capacity and the dropped coordinate carries no flow.
      intro j
      by_cases hj0 : j = j0
      · subst j
        simp only [xDrop, yDrop, if_neg hij0.symm, if_pos rfl, if_pos hj0C, mul_one]
        rw [hcoeff0_eq]
        linarith [min_le_right (a i) lam]
      · by_cases hji : j = i
        · subst j
          simp only [xDrop, yDrop, if_pos rfl, if_neg hij0, if_true, mul_zero, le_refl]
        · by_cases hjC : j ∈ C
          · simp only [xDrop, yDrop, if_neg hj0, if_neg hji, if_pos hjC, mul_one]
            exact le_refl (a j)
          · simp only [xDrop, yDrop, if_neg hj0, if_neg hji, if_neg hjC, mul_zero]
            exact le_refl (0 : ℝ)
  refine (mem_flow_cover_face_iff a b C (xDrop, yDrop)).2 ⟨?_, ?_⟩
  · exact subset_convexHull ℝ _ hpoint_mem
  · have hsupport : ∀ j ∈ Finset.univ, j ∉ C → yDrop j = 0 := by
      intro j hjUniv hjC
      have hj0 : j ≠ j0 := by
        intro hEq
        exact hjC (hEq ▸ hj0C)
      have hji : j ≠ i := by
        intro hEq
        exact hjC (hEq ▸ hiC)
      simp only [yDrop, if_neg hj0, if_neg hji, if_neg hjC]
    have hcover_sum : ∑ j ∈ C, yDrop j = b - coeffi := by
      calc
        ∑ j ∈ C, yDrop j = ∑ j, yDrop j :=
          Finset.sum_subset (Finset.subset_univ C) hsupport
        _ = b - coeffi := hsum_drop
    have hpenalty :
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (1 - xDrop j) = coeffi := by
      calc
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (1 - xDrop j) =
            flowCoverSupportCoeff a b C i * (1 - xDrop i) := by
          refine Finset.sum_eq_single_of_mem i hiC ?_
          intro j hjC hji
          simp only [xDrop, if_neg hji, if_pos hjC, sub_self, mul_zero]
        _ = coeffi := by
          simp only [xDrop, if_pos rfl, sub_zero, mul_one, coeffi]
    -- The lost cover flow is exactly restored by the unique selector penalty at `i`.
    rw [flow_cover_value_eq]
    change (∑ j ∈ C, yDrop j) +
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (1 - xDrop j) = b
    rw [hcover_sum, hpenalty]
    ring

/-- Helper for Theorem 7.9: subtracting two points on the equality face produces a direction
vector of the affine span of that face. -/
theorem flowCoverFaceSub_mem_direction
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {p q : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ flow_cover_face a b C)
    (hq : q ∈ flow_cover_face a b C) :
    p - q ∈ (affineSpan ℝ (flow_cover_face a b C)).direction := by
  have hq_aff : q ∈ affineSpan ℝ (flow_cover_face a b C) :=
    subset_affineSpan ℝ _ hq
  -- The difference of two face points is the corresponding `vsub` in the face direction.
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hq_aff]
  refine ⟨p, subset_affineSpan ℝ _ hp, ?_⟩
  simp [vsub_eq_sub]

/-- Helper for Theorem 7.9: subtracting the dropped-cover witness from the exchange witness gives
the exact coupled cover generator in the equality-face direction. -/
theorem flowCoverCoverXCoupled_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun j ↦ if j = i then 1 else 0),
        fun j ↦ if j = i then flowCoverSupportCoeff a b C i else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pEx : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then flowCoverSupportCoeff a b C j0 +
            min (a i) (flow_cover_excess a b C)
        else if j = i then a i - min (a i) (flow_cover_excess a b C)
        else if j ∈ C then a j else 0)
  let pDrop : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 0 else if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then flowCoverSupportCoeff a b C j0 +
            min (a i) (flow_cover_excess a b C)
        else if j = i then 0
        else if j ∈ C then a j else 0)
  have hpEx : pEx ∈ flow_cover_face a b C := by
    -- Reuse the exchange witness already placed on the equality face.
    simpa [pEx] using flowCoverCoverExchangePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hi
  have hpDrop : pDrop ∈ flow_cover_face a b C := by
    -- Reuse the dropped-cover witness already placed on the equality face.
    simpa [pDrop] using flowCoverCoverDropPoint_mem_face a b C ha_nonneg hC hj0C hj0lt hi
  have hdiff :
      pEx - pDrop =
        ((fun j ↦ if j = i then 1 else 0),
          fun j ↦ if j = i then flowCoverSupportCoeff a b C i else 0) := by
    have hi_mem := Finset.mem_erase.mp hi
    have hij0 : i ≠ j0 := hi_mem.1
    have hiC : i ∈ C := hi_mem.2
    have hcoeff_i :
        flowCoverSupportCoeff a b C i = a i - min (a i) (flow_cover_excess a b C) :=
      flowCoverSupportCoeff_eq_sub_min a b C hC i
    apply Prod.ext <;> funext j
    · by_cases hji : j = i
      · subst hji
        simp [pEx, pDrop, hiC]
      · by_cases hjC' : j ∈ C
        · simp [pEx, pDrop, hji, hjC']
        · simp [pEx, pDrop, hji, hjC']
    · by_cases hji : j = i
      · subst hji
        simp [pEx, pDrop, hij0, hcoeff_i]
      · by_cases hj0' : j = j0
        · subst hj0'
          simp [pEx, pDrop, hji]
        · by_cases hjC' : j ∈ C
          · simp [pEx, pDrop, hji, hj0', hjC']
          · simp [pEx, pDrop, hji, hj0', hjC']
  -- The coupled cover generator is exactly the difference between the exchange and drop witnesses.
  simpa [hdiff] using flowCoverFaceSub_mem_direction a b C hpEx hpDrop

/-- Helper for Theorem 7.9: subtracting the dropped-anchor witness from the anchor witness gives
the anchor coupled generator in the equality-face direction. -/
theorem flowCoverAnchorXCoupled_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    ((fun j ↦ if j = j0 then 1 else 0),
        fun j ↦ if j = j0 then flowCoverSupportCoeff a b C j0 else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pAnchor : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  let pDrop : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  have hpAnchor : pAnchor ∈ flow_cover_face a b C := by
    -- Reuse the canonical anchor witness on the equality face.
    simpa [pAnchor] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hpDrop : pDrop ∈ flow_cover_face a b C := by
    -- Reuse the dropped-anchor witness on the equality face.
    simpa [pDrop] using flowCoverDroppedAnchorPoint_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hcoeff_anchor :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C :=
    flowCoverSupportCoeff_anchor_eq a b C hC hj0lt
  have hdiff :
      pAnchor - pDrop =
        ((fun j ↦ if j = j0 then 1 else 0),
          fun j ↦ if j = j0 then flowCoverSupportCoeff a b C j0 else 0) := by
    apply Prod.ext <;> funext j
    · by_cases hji : j = j0
      · subst hji
        simp [pAnchor, pDrop, hj0C]
      · by_cases hjC' : j ∈ C
        · simp [pAnchor, pDrop, hji, hjC', Finset.mem_erase]
        · simp [pAnchor, pDrop, hji, hjC', Finset.mem_erase]
    · by_cases hji : j = j0
      · subst hji
        simp [pAnchor, pDrop, hj0C, hcoeff_anchor]
      · by_cases hjC' : j ∈ C
        · simp [pAnchor, pDrop, hji, hjC', Finset.mem_erase]
        · simp [pAnchor, pDrop, hji, hjC', Finset.mem_erase]
  -- The anchor coupled generator is the anchor witness minus the dropped-anchor witness.
  simpa [hdiff] using flowCoverFaceSub_mem_direction a b C hpAnchor hpDrop

/-- Helper for Theorem 7.9: toggling an outside selector gives the outside coordinate direction in
the equality-face direction. -/
theorem flowCoverOutsideCoordinateDirection_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun j ↦ if j = i then 1 else 0), fun _ ↦ (0 : ℝ)) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pToggle : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  let pDrop : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  have hpToggle : pToggle ∈ flow_cover_face a b C := by
    -- Reuse the outside-toggle witness on the equality face.
    simpa [pToggle] using flowCoverOutsideTogglePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hiC
  have hpDrop : pDrop ∈ flow_cover_face a b C := by
    -- Reuse the dropped-anchor witness on the equality face.
    simpa [pDrop] using flowCoverDroppedAnchorPoint_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hdiff :
      pToggle - pDrop = ((fun j ↦ if j = i then 1 else 0), fun _ ↦ (0 : ℝ)) := by
    apply Prod.ext <;> funext j
    · by_cases hji : j = i
      · subst hji
        simp [pToggle, pDrop, hiC]
      · by_cases hj : j ∈ C.erase j0
        · simp [pToggle, pDrop, hji]
        · simp [pToggle, pDrop, hji]
    · by_cases hj : j ∈ C.erase j0
      · simp [pToggle, pDrop]
      · simp [pToggle, pDrop]
  -- The outside coordinate generator is the toggle witness minus the dropped-anchor witness.
  simpa [hdiff] using flowCoverFaceSub_mem_direction a b C hpToggle hpDrop

/-- Helper for Theorem 7.9: adding outside flow on top of the outside toggle witness gives the
outside flow coordinate direction in the equality-face direction. -/
theorem flowCoverOutsideFlowDirection_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun _ ↦ (0 : ℝ)),
        fun j ↦ if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pFlow : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j
        else if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0)
  let pToggle : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  have hpFlow : pFlow ∈ flow_cover_face a b C := by
    -- Reuse the outside-flow witness on the equality face.
    simpa [pFlow] using flowCoverOutsideFlowPoint_mem_face a b C ha_nonneg hC hj0C hj0lt hiC
  have hpToggle : pToggle ∈ flow_cover_face a b C := by
    -- Reuse the outside-toggle witness on the equality face.
    simpa [pToggle] using flowCoverOutsideTogglePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hiC
  have hdiff :
      pFlow - pToggle =
        ((fun _ ↦ (0 : ℝ)),
          fun j ↦ if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0) := by
    apply Prod.ext <;> funext j
    · by_cases hji : j = i
      · subst hji
        simp [pFlow, pToggle]
      · by_cases hj : j ∈ C.erase j0
        · simp [pFlow, pToggle]
        · simp [pFlow, pToggle]
    · by_cases hji : j = i
      · subst hji
        simp [pFlow, pToggle, hiC]
      · by_cases hj : j ∈ C.erase j0
        · simp [pFlow, pToggle, hji]
        · simp [pFlow, pToggle, hji]
  -- The outside flow generator is the outside-flow witness minus the toggle witness.
  simpa [hdiff] using flowCoverFaceSub_mem_direction a b C hpFlow hpToggle

/-- Helper for Theorem 7.9: exchanging `min (a_i) λ` units of cover flow from `i` to the anchor
gives the cover `y`-difference direction inside the equality-face direction. -/
theorem flowCoverCoverYExchange_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun _ ↦ (0 : ℝ)),
        fun j ↦
          if j = j0 then min (a i) (flow_cover_excess a b C)
          else if j = i then -min (a i) (flow_cover_excess a b C)
          else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pEx : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then flowCoverSupportCoeff a b C j0 +
            min (a i) (flow_cover_excess a b C)
        else if j = i then a i - min (a i) (flow_cover_excess a b C)
        else if j ∈ C then a j else 0)
  let pAnchor : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  have hpEx : pEx ∈ flow_cover_face a b C := by
    -- Reuse the cover-exchange witness on the equality face.
    simpa [pEx] using flowCoverCoverExchangePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hi
  have hpAnchor : pAnchor ∈ flow_cover_face a b C := by
    -- Reuse the canonical anchor witness on the equality face.
    simpa [pAnchor] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hi_mem := Finset.mem_erase.mp hi
  have hij0 : i ≠ j0 := hi_mem.1
  have hiC : i ∈ C := hi_mem.2
  have hcoeff_anchor :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C :=
    flowCoverSupportCoeff_anchor_eq a b C hC hj0lt
  have hdiff :
      pEx - pAnchor =
        ((fun _ ↦ (0 : ℝ)),
          fun j ↦
            if j = j0 then min (a i) (flow_cover_excess a b C)
            else if j = i then -min (a i) (flow_cover_excess a b C)
            else 0) := by
    apply Prod.ext <;> funext j
    · by_cases hjC' : j ∈ C
      · simp [pEx, pAnchor]
      · simp [pEx, pAnchor]
    · by_cases hj0' : j = j0
      · subst hj0'
        simp [pEx, pAnchor, hj0C, hcoeff_anchor]
      · by_cases hji : j = i
        · subst hji
          simp [pEx, pAnchor, hj0', hiC]
        · by_cases hjC' : j ∈ C
          · simp [pEx, pAnchor, hj0', hji, hjC']
          · simp [pEx, pAnchor, hj0', hji, hjC']
  -- The cover-flow transfer is the exchange witness minus the anchor witness.
  simpa [hdiff] using flowCoverFaceSub_mem_direction a b C hpEx hpAnchor

/-- Helper for Theorem 7.9: any outside-supported pair belongs to the flow-cover face direction,
provided zero-capacity coordinates contribute no outside flow. -/
theorem flowCoverOutsideSupportedPair_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C)
    (sx sy : ℝ)
    (hsy_zero : a i = 0 → sy = 0) :
    ((fun j ↦ if j = i then sx else 0),
        fun j ↦ if j = i then sy else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let FD : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (flow_cover_face a b C)).direction
  let coeff0 : ℝ := flowCoverSupportCoeff a b C j0
  let m : ℝ := min (a i) coeff0
  let gX : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else 0), fun _ ↦ 0)
  let gY : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun _ ↦ 0), fun j ↦ if j = i then m else 0)
  have hgX : gX ∈ FD := by
    simpa only [gX, FD] using
      flowCoverOutsideCoordinateDirection_mem_faceDirection
        a b C ha_nonneg hC hj0C hj0lt hiC
  have hgY : gY ∈ FD := by
    simpa only [gY, m, coeff0, FD] using
      flowCoverOutsideFlowDirection_mem_faceDirection
        a b C ha_nonneg hC hj0C hj0lt hiC
  by_cases hai : a i = 0
  · have hsy : sy = 0 := hsy_zero hai
    have hscaled : sx • gX ∈ FD := FD.smul_mem sx hgX
    have hcombination :
        ((fun j ↦ if j = i then sx else 0), fun j ↦ if j = i then sy else 0) =
          sx • gX := by
      apply Prod.ext <;> funext j
      · by_cases hji : j = i
        · subst j
          simp [gX]
        · simp [gX, hji]
      · simp [gX, hsy]
    -- With zero capacity the flow component vanishes, leaving only the selector generator.
    rw [hcombination]
    exact hscaled
  · have hai_pos : 0 < a i := lt_of_le_of_ne (ha_nonneg i) (Ne.symm hai)
    have hcoeff0_pos : 0 < coeff0 := by
      have hcoeff0_eq : coeff0 = a j0 - flow_cover_excess a b C := by
        simpa only [coeff0] using
          flowCoverSupportCoeff_anchor_eq a b C hC hj0lt
      rw [hcoeff0_eq]
      linarith
    have hm_pos : 0 < m := by
      exact lt_min hai_pos hcoeff0_pos
    have hcombination :
        ((fun j ↦ if j = i then sx else 0), fun j ↦ if j = i then sy else 0) =
          sx • gX + (sy / m) • gY := by
      apply Prod.ext <;> funext j
      · by_cases hji : j = i
        · subst j
          simp [gX, gY]
        · simp [gX, gY, hji]
      · by_cases hji : j = i
        · subst j
          simp [gX, gY, hm_pos.ne']
        · simp [gX, gY, hji]
    -- Scale the selector and flow generators independently, then add them.
    rw [hcombination]
    exact FD.add_mem (FD.smul_mem sx hgX) (FD.smul_mem (sy / m) hgY)

/-- Helper for Theorem 7.9: any non-anchor cover-supported pair with the required anchor
compensation lies in the flow-cover face direction. -/
theorem flowCoverCoverSupportedPair_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0)
    (sx sy : ℝ)
    (hsy_zero : a i = 0 → sy = 0) :
    ((fun j ↦ if j = i then sx else 0),
        fun j ↦
          if j = j0 then flowCoverSupportCoeff a b C i * sx - sy
          else if j = i then sy else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let FD : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (flow_cover_face a b C)).direction
  let lam : ℝ := flow_cover_excess a b C
  let m : ℝ := min (a i) lam
  let coeffi : ℝ := flowCoverSupportCoeff a b C i
  let gX : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else 0), fun j ↦ if j = i then coeffi else 0)
  let gY : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun _ ↦ 0), fun j ↦ if j = j0 then m else if j = i then -m else 0)
  have hi_mem := Finset.mem_erase.mp hi
  have hij0 : i ≠ j0 := hi_mem.1
  have hgX : gX ∈ FD := by
    simpa only [gX, coeffi, FD] using
      flowCoverCoverXCoupled_mem_faceDirection
        a b C ha_nonneg hC hj0C hj0lt hi
  have hgY : gY ∈ FD := by
    simpa only [gY, m, lam, FD] using
      flowCoverCoverYExchange_mem_faceDirection
        a b C ha_nonneg hC hj0C hj0lt hi
  by_cases hai : a i = 0
  · have hsy : sy = 0 := hsy_zero hai
    have hlam_pos : 0 < lam := by
      simpa only [lam] using flow_cover_excess_pos a b C hC
    have hcoeffi_zero : flowCoverSupportCoeff a b C i = 0 := by
      rw [flowCoverSupportCoeff_eq_sub_min a b C hC i, hai]
      rw [min_eq_left]
      · ring
      · exact hlam_pos.le
    have hcoeffi_zero_local : coeffi = 0 := by
      simpa only [coeffi] using hcoeffi_zero
    have hcombination :
        ((fun j ↦ if j = i then sx else 0),
            fun j ↦ if j = j0 then flowCoverSupportCoeff a b C i * sx - sy
              else if j = i then sy else 0) = sx • gX := by
      apply Prod.ext <;> funext j
      · by_cases hji : j = i
        · subst j
          simp [gX]
        · simp [gX, hji]
      · by_cases hj0 : j = j0
        · subst j
          simp [gX, hcoeffi_zero, hcoeffi_zero_local, hsy]
        · by_cases hji : j = i
          · subst j
            simp [gX, hcoeffi_zero_local, hsy, hij0]
          · simp [gX, hj0, hji, hcoeffi_zero_local]
    have hscaled : sx • gX ∈ FD := FD.smul_mem sx hgX
    -- At zero capacity both the requested flow and its support coefficient vanish.
    rw [hcombination]
    exact hscaled
  · have hai_pos : 0 < a i := lt_of_le_of_ne (ha_nonneg i) (Ne.symm hai)
    have hlam_pos : 0 < lam := by
      simpa only [lam] using flow_cover_excess_pos a b C hC
    have hm_pos : 0 < m := lt_min hai_pos hlam_pos
    let t : ℝ := (coeffi * sx - sy) / m
    have hcombination :
        ((fun j ↦ if j = i then sx else 0),
            fun j ↦ if j = j0 then coeffi * sx - sy else if j = i then sy else 0) =
          sx • gX + t • gY := by
      apply Prod.ext <;> funext j
      · by_cases hji : j = i
        · subst j
          simp [gX, gY]
        · simp [gX, gY, hji]
      · by_cases hj0 : j = j0
        · subst j
          have hj0i : j0 ≠ i := hij0.symm
          simp [gX, gY, t, hj0i, hm_pos.ne']
        · by_cases hji : j = i
          · subst j
            simp [gX, gY, t, hij0, hm_pos.ne']
            field_simp
            ring
          · simp [gX, gY, hj0, hji]
    -- The coefficient of the transfer generator supplies exactly the anchor compensation.
    rw [hcombination]
    exact FD.add_mem (FD.smul_mem sx hgX) (FD.smul_mem t hgY)

/-- Helper for Theorem 7.9: subtracting a scaled face-direction generator from an ambient
support-kernel vector keeps the residual inside the same ambient support-kernel cut. -/
theorem supportKerSubSmul_mem
    {FD D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ))}
    {L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ}
    (hFD_le : FD ≤ D ⊓ LinearMap.ker L)
    {u g : (Fin n → ℝ) × (Fin n → ℝ)} (hu : u ∈ D ⊓ LinearMap.ker L) (hg : g ∈ FD)
    (t : ℝ) :
    u - t • g ∈ D ⊓ LinearMap.ker L := by
  -- Push the generator into the ambient support-kernel cut, then use submodule closure.
  exact sub_mem hu ((D ⊓ LinearMap.ker L).smul_mem t (hFD_le hg))

/-- Helper for Theorem 7.9: the remaining source-faithful step is to show that the anchored
textbook witness family spans every ambient support-kernel direction of the flow-cover face. -/
theorem flowCoverFaceDirection_eq_polyDirection_inf_supportKer
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    (affineSpan ℝ (flow_cover_face a b C)).direction =
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction ⊓ LinearMap.ker L := by
  classical
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  dsimp
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
  let FD : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (flow_cover_face a b C)).direction
  change FD = D ⊓ LinearMap.ker L
  apply le_antisymm
  · -- The supporting equation gives the direct inclusion of face directions.
    simpa only [FD, D, L, coeff] using
      flowCoverFaceDirection_le_polyDirection_inf_supportKer
        a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩
  · intro u hu
    let outsideTerm : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) := fun i ↦
      ((fun j ↦ if j = i then u.1 i else 0), fun j ↦ if j = i then u.2 i else 0)
    let coverTerm : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) := fun i ↦
      ((fun j ↦ if j = i then u.1 i else 0),
        fun j ↦ if j = j0 then coeff i * u.1 i - u.2 i
          else if j = i then u.2 i else 0)
    let anchorTerm : (Fin n → ℝ) × (Fin n → ℝ) :=
      u.1 j0 •
        ((fun j ↦ if j = j0 then 1 else 0), fun j ↦ if j = j0 then coeff j0 else 0)
    have hkernel : L u = 0 := hu.2
    change (∑ j ∈ C, u.2 j) - ∑ j ∈ C, coeff j * u.1 j = 0 at hkernel
    have hy_split :
        ∑ j ∈ C, u.2 j = (∑ j ∈ C.erase j0, u.2 j) + u.2 j0 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := C) (f := u.2) hj0C).symm
    have hx_split :
        ∑ j ∈ C, coeff j * u.1 j =
          (∑ j ∈ C.erase j0, coeff j * u.1 j) + coeff j0 * u.1 j0 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := C) (f := fun j ↦ coeff j * u.1 j) hj0C).symm
    have hanchor_balance :
        u.2 j0 = coeff j0 * u.1 j0 +
          ∑ i ∈ C.erase j0, (coeff i * u.1 i - u.2 i) := by
      rw [Finset.sum_sub_distrib]
      rw [hy_split, hx_split] at hkernel
      linarith
    have houtside_mem : ∑ i ∈ Finset.univ \ C, outsideTerm i ∈ FD := by
      refine Submodule.sum_mem FD ?_
      intro i hi
      have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
      have hzero : a i = 0 → u.2 i = 0 := by
        intro hai
        exact singleNodeFlowAmbientDirection_y_zero_of_capacity_zero
          a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩ hu.1 hai
      simpa only [outsideTerm, FD] using
        flowCoverOutsideSupportedPair_mem_faceDirection
          a b C ha_nonneg hC hj0C hj0lt hiC (u.1 i) (u.2 i) hzero
    have hcover_mem : ∑ i ∈ C.erase j0, coverTerm i ∈ FD := by
      refine Submodule.sum_mem FD ?_
      intro i hi
      have hzero : a i = 0 → u.2 i = 0 := by
        intro hai
        exact singleNodeFlowAmbientDirection_y_zero_of_capacity_zero
          a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩ hu.1 hai
      simpa only [coverTerm, coeff, FD] using
        flowCoverCoverSupportedPair_mem_faceDirection
          a b C ha_nonneg hC hj0C hj0lt hi (u.1 i) (u.2 i) hzero
    have hanchor_generator :
        ((fun j ↦ if j = j0 then 1 else 0),
            fun j ↦ if j = j0 then coeff j0 else 0) ∈ FD := by
      simpa only [coeff, FD] using
        flowCoverAnchorXCoupled_mem_faceDirection a b C ha_nonneg hC hj0C hj0lt
    have hanchor_mem : anchorTerm ∈ FD := by
      exact FD.smul_mem (u.1 j0) hanchor_generator
    have hsingle_sum (S : Finset (Fin n)) (z : Fin n → ℝ) (k : Fin n) :
        (∑ i ∈ S, if k = i then z i else 0) = if k ∈ S then z k else 0 := by
      by_cases hk : k ∈ S
      · rw [if_pos hk]
        rw [Finset.sum_eq_single_of_mem k hk]
        · rw [if_pos rfl]
        · intro i hi hki
          rw [if_neg]
          exact Ne.symm hki
      · rw [if_neg hk]
        refine Finset.sum_eq_zero ?_
        intro i hi
        rw [if_neg]
        intro hki
        subst i
        exact hk hi
    have houtside_fst (k : Fin n) :
        (∑ i ∈ Finset.univ \ C, outsideTerm i).1 k =
          if k ∈ Finset.univ \ C then u.1 k else 0 := by
      rw [Prod.fst_sum, Finset.sum_apply]
      simp only [outsideTerm]
      exact hsingle_sum (Finset.univ \ C) u.1 k
    have houtside_snd (k : Fin n) :
        (∑ i ∈ Finset.univ \ C, outsideTerm i).2 k =
          if k ∈ Finset.univ \ C then u.2 k else 0 := by
      rw [Prod.snd_sum, Finset.sum_apply]
      simp only [outsideTerm]
      exact hsingle_sum (Finset.univ \ C) u.2 k
    have hcover_fst (k : Fin n) :
        (∑ i ∈ C.erase j0, coverTerm i).1 k =
          if k ∈ C.erase j0 then u.1 k else 0 := by
      rw [Prod.fst_sum, Finset.sum_apply]
      simp only [coverTerm]
      exact hsingle_sum (C.erase j0) u.1 k
    have hcover_snd_anchor :
        (∑ i ∈ C.erase j0, coverTerm i).2 j0 =
          ∑ i ∈ C.erase j0, (coeff i * u.1 i - u.2 i) := by
      rw [Prod.snd_sum, Finset.sum_apply]
      simp only [coverTerm, if_true]
    have hcover_snd (k : Fin n) (hk0 : k ≠ j0) :
        (∑ i ∈ C.erase j0, coverTerm i).2 k =
          if k ∈ C.erase j0 then u.2 k else 0 := by
      rw [Prod.snd_sum, Finset.sum_apply]
      simp only [coverTerm, if_neg hk0]
      exact hsingle_sum (C.erase j0) u.2 k
    have hdecomp :
        u = (∑ i ∈ Finset.univ \ C, outsideTerm i) +
          (∑ i ∈ C.erase j0, coverTerm i) + anchorTerm := by
      apply Prod.ext
      · funext k
        simp only [Prod.fst_add, Pi.add_apply]
        by_cases hk0 : k = j0
        · subst k
          have hj0Outside : j0 ∉ Finset.univ \ C := by simp [hj0C]
          have hj0Erase : j0 ∉ C.erase j0 := by simp
          rw [houtside_fst, hcover_fst]
          simp only [if_neg hj0Outside, if_neg hj0Erase, anchorTerm, Prod.smul_fst,
            Pi.smul_apply, if_true, smul_eq_mul, mul_one, zero_add]
        · by_cases hkC : k ∈ C
          · have hkErase : k ∈ C.erase j0 := Finset.mem_erase.mpr ⟨hk0, hkC⟩
            have hkOutside : k ∉ Finset.univ \ C := by simp [hkC]
            rw [houtside_fst, hcover_fst]
            simp only [if_neg hkOutside, if_pos hkErase, anchorTerm, Prod.smul_fst,
              Pi.smul_apply, if_neg hk0, smul_eq_mul, mul_zero, zero_add, add_zero]
          · have hkOutside : k ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkC⟩
            have hkErase : k ∉ C.erase j0 := by
              intro hk
              exact hkC (Finset.mem_erase.mp hk).2
            rw [houtside_fst, hcover_fst]
            simp only [if_pos hkOutside, if_neg hkErase, anchorTerm, Prod.smul_fst,
              Pi.smul_apply, if_neg hk0, smul_eq_mul, mul_zero, add_zero]
      · funext k
        simp only [Prod.snd_add, Pi.add_apply]
        by_cases hk0 : k = j0
        · subst k
          have hj0Outside : j0 ∉ Finset.univ \ C := by simp [hj0C]
          rw [houtside_snd, hcover_snd_anchor]
          simp only [if_neg hj0Outside, anchorTerm, Prod.smul_snd, Pi.smul_apply,
            if_true, smul_eq_mul, zero_add]
          rw [hanchor_balance]
          ring
        · by_cases hkC : k ∈ C
          · have hkErase : k ∈ C.erase j0 := Finset.mem_erase.mpr ⟨hk0, hkC⟩
            have hkOutside : k ∉ Finset.univ \ C := by simp [hkC]
            rw [houtside_snd, hcover_snd k hk0]
            simp only [if_neg hkOutside, if_pos hkErase, anchorTerm, Prod.smul_snd,
              Pi.smul_apply, if_neg hk0, smul_eq_mul, mul_zero, zero_add, add_zero]
          · have hkOutside : k ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkC⟩
            have hkErase : k ∉ C.erase j0 := by
              intro hk
              exact hkC (Finset.mem_erase.mp hk).2
            rw [houtside_snd, hcover_snd k hk0]
            simp only [if_pos hkOutside, if_neg hkErase, anchorTerm, Prod.smul_snd,
              Pi.smul_apply, if_neg hk0, smul_eq_mul, mul_zero, add_zero]
    -- The three supported families reconstruct every ambient kernel vector coordinatewise.
    rw [hdecomp]
    exact FD.add_mem (FD.add_mem houtside_mem hcover_mem) hanchor_mem

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_9.lean

Theorem 7.9 (2). Let `C` be a flow cover for the single-node flow set `T`, and let
`λ = ∑_{j ∈ C} a_j - b`. If some `j ∈ C` satisfies `λ < a_j` (equivalently,
`λ < max_{j ∈ C} a_j`), then the flow cover inequality defined by `C` cuts out a facet of
`conv(T)`. -/
theorem single_node_flow_cover_inequality_facet
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C) := by
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  rw [isFacetOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- The standard anchor point gives an explicit point on the equality face.
    exact ⟨_, flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt⟩
  · -- The exposed-face part was proved separately from the codimension computation.
    exact flow_cover_face_isExposed a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩
  · let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
    have hdir_eq :
        (affineSpan ℝ (flow_cover_face a b C)).direction =
          D ⊓ LinearMap.ker L := by
      -- Route correction: the remaining bridge is the source witness-family reverse inclusion.
      simpa [coeff, L, D] using
        flowCoverFaceDirection_eq_polyDirection_inf_supportKer
          a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩
    have hcodim :
        Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
      -- The ambient support-kernel cut already has codimension one.
      simpa [coeff, L, D] using
        flowCoverSupportKerCodimOne a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩
    calc
      Module.finrank ℝ (affineSpan ℝ (flow_cover_face a b C)).direction + 1
          = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 := by
              rw [hdir_eq]
      _ = Module.finrank ℝ ↥D := hcodim
      _ = Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction := by
            rfl

end Theorem79
