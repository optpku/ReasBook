/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open WithLp

universe u v

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

section ProductL2Bridge

/-- Canonical raw-product `ℓ²` pseudometric bridge: view `H × K` with the metric transported from
`WithLp 2 (H × K)`. Downstream files activate it locally when they need the textbook Hilbert
geometry on the raw product type. -/
noncomputable abbrev prod_pseudoMetricSpace_l2 : PseudoMetricSpace (H × K) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) H K

/-- Canonical raw-product `ℓ²` norm bridge: equip `H × K` with the norm transported from
`WithLp 2 (H × K)`. -/
noncomputable abbrev prod_normedAddCommGroup_l2 : NormedAddCommGroup (H × K) :=
  WithLp.normedAddCommGroupToProd (p := 2) H K

/-- Canonical raw-product `ℓ²` seminorm bridge on `H × K`. This is the primitive `WithLp` owner
needed to derive the scalar-action structure. -/
noncomputable abbrev prod_seminormedAddCommGroup_l2 : SeminormedAddCommGroup (H × K) :=
  WithLp.seminormedAddCommGroupToProd (p := 2) H K

local instance prod_seminormedAddCommGroup_l2_inst : SeminormedAddCommGroup (H × K) :=
  prod_seminormedAddCommGroup_l2 (H := H) (K := K)

local instance prod_normedAddCommGroup_l2_inst : NormedAddCommGroup (H × K) :=
  prod_normedAddCommGroup_l2 (H := H) (K := K)

/-- Canonical raw-product `ℓ²` scalar-action bridge on `H × K`. -/
noncomputable abbrev prod_normedSpace_l2 : NormedSpace ℝ (H × K) := by
  letI : NormedAddCommGroup (H × K) := prod_normedAddCommGroup_l2 (H := H) (K := K)
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd 2 H K

local instance prod_normedSpace_l2_inst : NormedSpace ℝ (H × K) :=
  prod_normedSpace_l2 (H := H) (K := K)

/-- Canonical raw-product `ℓ²` completeness bridge on `H × K`. -/
noncomputable abbrev prod_completeSpace_l2 [CompleteSpace H] [CompleteSpace K] :
    CompleteSpace (H × K) :=
  by
    letI : PseudoMetricSpace (H × K) := prod_pseudoMetricSpace_l2 (H := H) (K := K)
    exact (WithLp.uniformEquivProd (p := 2) H K).completeSpace_iff.1 inferInstance

/-- Canonical raw-product `ℓ²` Hilbert bridge on `H × K`, with inner product
`⟪(u₁, v₁), (u₂, v₂)⟫ = ⟪u₁, u₂⟫ + ⟪v₁, v₂⟫`. -/
noncomputable abbrev prod_innerProductSpace_l2 : InnerProductSpace ℝ (H × K) := by
  letI : NormedAddCommGroup (H × K) := prod_normedAddCommGroup_l2 (H := H) (K := K)
  letI : NormedSpace ℝ (H × K) := prod_normedSpace_l2 (H := H) (K := K)
  exact
    { inner x y := ⟪x.1, y.1⟫_ℝ + ⟪x.2, y.2⟫_ℝ
      norm_sq_eq_re_inner x := by
        have hnorm : ‖x‖ = ‖WithLp.toLp 2 x‖ := by
          simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
            (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := K) x)
        have hnorm_sq : ‖x‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
          simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
        exact hnorm_sq.trans <| by
          simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 x))
      conj_inner_symm x y := by
        simp [real_inner_comm]
      add_left x y z := by
        simp [inner_add_left, add_assoc, add_left_comm]
      smul_left x y r := by
        simp [inner_smul_left, mul_add] }

end ProductL2Bridge

section EpigraphProjection

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance prod_pseudoMetricSpace_l2_real : PseudoMetricSpace (H × ℝ) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ

local instance prod_normedAddCommGroup_l2_real : NormedAddCommGroup (H × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) H ℝ

local instance prod_seminormedAddCommGroup_l2_real : SeminormedAddCommGroup (H × ℝ) :=
  WithLp.seminormedAddCommGroupToProd (p := 2) H ℝ

local instance prod_normedSpace_l2_real : NormedSpace ℝ (H × ℝ) :=
  by
    letI : NormedAddCommGroup (H × ℝ) := prod_normedAddCommGroup_l2_real
    exact WithLp.normedSpaceSeminormedAddCommGroupToProd 2 H ℝ

local instance prod_completeSpace_l2_real : CompleteSpace (H × ℝ) :=
  by
    letI : PseudoMetricSpace (H × ℝ) := WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ
    exact (WithLp.uniformEquivProd (p := 2) H ℝ).completeSpace_iff.1 inferInstance

local instance prod_innerProductSpace_l2_real : InnerProductSpace ℝ (H × ℝ) where
  inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
  norm_sq_eq_re_inner x := by
    have hnorm : ‖x‖ = ‖WithLp.toLp 2 x‖ := by
      simpa [prod_normedAddCommGroup_l2_real, prod_seminormedAddCommGroup_l2_real] using
        (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := ℝ) x)
    have hnorm_sq : ‖x‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
      simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
    exact hnorm_sq.trans <| by
      simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 x))
  conj_inner_symm x y := by
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

/-
The next helper does not use completeness; keep the signature minimal so the file stays
warning-free.
-/
omit [CompleteSpace H] in
/-- Helper for Proposition 9.18: `Γ₀(H)` convexity on the effective domain is equivalent to
convexity of the real-height epigraph. -/
theorem convex_epigraph_of_mem_gammaZero {f : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) :
    Convex ℝ (epigraph (fun y : H ↦ (f y : EReal))) := by
  -- Translate the stored Jensen inequality on `effectiveDomain f` to the `dom` formulation used by
  -- `convex_epigraph_iff_jensen_on_dom`.
  refine (convex_epigraph_iff_jensen_on_dom (fun y : H ↦ (f y : EReal))).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  simpa using hf.2.ineq hx' hy' hα hα_lt_one

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 9.18: every effective-domain point yields its canonical real-height
epigraph point at ordinate `(f y).toReal`. -/
private lemma mem_epigraph_toReal_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∈ effectiveDomain f) :
    (y, (f y : EReal).toReal) ∈ epigraph (fun z : H ↦ (f z : EReal)) := by
  -- Finiteness of `f y` exactly says that the `toReal` ordinate sits on or above the epigraph.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hy))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 9.18: a real-height epigraph point has base point in the effective
domain, and its ordinate dominates `(f y).toReal`. -/
private lemma effectiveDomain_and_toReal_le_of_mem_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph (fun z : H ↦ (f z : EReal))) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- The real ordinate `η` is finite, so epigraph membership first forces `y` into the effective
  -- domain; then `toReal` preserves the comparison against the finite height.
  have hfy_le : (f y : EReal) ≤ (η : EReal) := (mem_epigraph_iff _ _ _).mp hyη
  have hy_dom : y ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfy_le (EReal.coe_lt_top η)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hη_top : (η : EReal) ≠ ⊤ := EReal.coe_ne_top η
  have htoReal : (f y : EReal).toReal ≤ ((η : EReal)).toReal := by
    simpa using EReal.toReal_le_toReal hfy_le hfy_bot hη_top
  simpa using ⟨hy_dom, htoReal⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 9.18: the product Hilbert inner product on `H × ℝ` splits into its
`H`-component and scalar component after translating by `(p, π)`. -/
private lemma inner_sub_prod_eq {x y p : H} {ξ η π : ℝ} :
    ⟪(y, η) - (p, π), (x, ξ) - (p, π)⟫_ℝ =
      ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) := by
  letI : InnerProductSpace ℝ (H × ℝ) := prod_innerProductSpace_l2_real (H := H)
  change ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) =
      ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π)
  rfl

-- Proof sketch: a function in `Γ₀(H)` has nonempty effective domain, closed real-height epigraph,
-- and convex epigraph. Combine these facts and apply
-- `isChebyshev_of_nonempty_isClosed_convex` in the product Hilbert space `H × ℝ`.
/-- The real-height epigraph of a `Γ₀(H)` function is a Chebyshev subset of `H × ℝ`. -/
theorem isChebyshev_epigraph_of_mem_gammaZero {f : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) :
    IsChebyshev (epigraph (fun y : H ↦ (f y : EReal)) : Set (H × ℝ)) := by
  -- Package the geometric inputs needed by the Hilbert projection theorem.
  have hnonempty :
      (epigraph (fun y : H ↦ (f y : EReal)) : Set (H × ℝ)).Nonempty := by
    rcases hf.2.nonempty with ⟨y, hy⟩
    exact ⟨(y, (f y : EReal).toReal), mem_epigraph_toReal_of_mem_effectiveDomain hy⟩
  have hclosed :
      IsClosed (epigraph (fun y : H ↦ (f y : EReal)) : Set (H × ℝ)) := by
    -- Lower semicontinuity is equivalent to closedness of the real-height epigraph.
    exact (lowerSemicontinuous_iff_isClosed_epigraph (fun y : H ↦ (f y : EReal))).1 hf.1
  have hconv :
      Convex ℝ (epigraph (fun y : H ↦ (f y : EReal)) : Set (H × ℝ)) :=
    by simpa using convex_epigraph_of_mem_gammaZero (H := H) hf
  -- The closed convex epigraph is therefore a Chebyshev set in the product Hilbert space.
  exact isChebyshev_of_nonempty_isClosed_convex hnonempty hclosed hconv

-- Proof sketch: apply the projection characterization from Theorem 3.16 to the closed convex set
-- `epigraph (fun y ↦ (f y : EReal))`. Rewrite epigraph membership with `mem_epigraph_iff`, use the
-- effective-domain condition to pass from finite `EReal` values to real heights, and separate the
-- product-space inner product into its `H` and `ℝ` components.
/-- Proposition 9.18: for `f ∈ Γ₀(H)`, a pair `(p, π)` is the metric projection of `(x, ξ)` onto
the real-height epigraph of `f` if and only if `π` majorizes both `ξ` and `f p`, and the
resulting variational inequality holds against every point of `effectiveDomain f`. -/
theorem eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ} :
    (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) ↔
      max (ξ : EReal) (f p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain f,
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 := by
  let C : Set (H × ℝ) := epigraph (fun y : H ↦ (f y : EReal))
  have hC_convex : Convex ℝ C := by
    -- The `Γ₀` hypothesis gives the convexity input for the projection characterization.
    simpa [C] using convex_epigraph_of_mem_gammaZero hf
  have hproj_iff :
      (p, π) = projectionPoint C (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) ↔
        (p, π) ∈ C ∧
          ∀ z ∈ C, ⟪z - (p, π), (x, ξ) - (p, π)⟫_ℝ ≤ 0 := by
    -- Route correction: work in the `ℓ²` product Hilbert space on `H × ℝ`, so Theorem 3.16
    -- applies directly to the real-height epigraph.
    simpa [C] using
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (C := C) (hC := isChebyshev_epigraph_of_mem_gammaZero hf) hC_convex
        (x := (x, ξ)) (p := (p, π)))
  constructor
  · intro hproj
    rcases hproj_iff.mp (by simpa [C] using hproj) with ⟨hpC, hproj_var⟩
    have hp_le : (f p : EReal) ≤ (π : EReal) := by
      simpa [C] using hpC
    have hp_high : (p, π + 1) ∈ C := by
      -- Testing the projection inequality at the higher point `(p, π + 1)` forces `ξ ≤ π`.
      change (f p : EReal) ≤ ((π + 1 : ℝ) : EReal)
      exact le_trans hp_le (by exact_mod_cast le_add_of_nonneg_right (show 0 ≤ (1 : ℝ) by norm_num))
    have hξ_sub_nonpos : ξ - π ≤ 0 := by
      have hraw :
          ⟪(p, π + 1) - (p, π), (x, ξ) - (p, π)⟫_ℝ ≤ 0 :=
        hproj_var (p, π + 1) hp_high
      rw [inner_sub_prod_eq] at hraw
      simpa using hraw
    have hξ_le_pi : ξ ≤ π := sub_nonpos.mp hξ_sub_nonpos
    have hξ_le : (ξ : EReal) ≤ (π : EReal) := by
      exact_mod_cast hξ_le_pi
    refine ⟨max_le hξ_le hp_le, ?_⟩
    intro y hy
    have hyC : (y, (f y : EReal).toReal) ∈ C := by
      simpa [C] using mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hy
    -- Evaluating the product-space inequality at the canonical real-height epigraph point
    -- gives exactly the domain-level variational inequality.
    simpa [C] using hproj_var (y, (f y : EReal).toReal) hyC
  · rintro ⟨hmax, hvar⟩
    have hp_mem : (p, π) ∈ C := by
      -- The max-bound contains the ordinary epigraph membership of `(p, π)`.
      change (f p : EReal) ≤ (π : EReal)
      exact le_trans (le_max_right (ξ : EReal) (f p : EReal)) hmax
    have hξ_le : ξ ≤ π := by
      exact_mod_cast
        (le_trans (le_max_left (ξ : EReal) (f p : EReal)) hmax :
          (ξ : EReal) ≤ (π : EReal))
    refine hproj_iff.mpr ⟨hp_mem, ?_⟩
    rintro ⟨y, η⟩ hyη
    rcases effectiveDomain_and_toReal_le_of_mem_epigraph
        (f := f) (by simpa [C] using hyη) with ⟨hy, hfy_le_eta⟩
    have hscalar :
        (η - π) * (ξ - π) ≤ ((f y : EReal).toReal - π) * (ξ - π) := by
      -- Since `ξ - π ≤ 0`, increasing the height from `(f y).toReal` to `η` only decreases the
      -- scalar contribution in the variational inequality.
      exact
        mul_le_mul_of_nonpos_right
          (sub_le_sub_right hfy_le_eta π) (sub_nonpos.mpr hξ_le)
    have hsum :
        ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) ≤
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hscalar ⟪y - p, x - p⟫_ℝ
    -- The domain-level inequality controls the canonical height, and monotonicity in the second
    -- coordinate extends it to every epigraph point.
    calc
      ⟪(y, η) - (p, π), (x, ξ) - (p, π)⟫_ℝ
          = ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) := inner_sub_prod_eq
      _ ≤ ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) := hsum
      _ ≤ 0 := hvar y hy

end EpigraphProjection

end

end ERealFunction
