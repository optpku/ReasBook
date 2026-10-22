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

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 9.21: view `H × ℝ` with the `ℓ²` product metric used by the epigraph
projection argument. -/
local instance prod_pseudoMetricSpace_l2_cor921 : PseudoMetricSpace (H × ℝ) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ

/-- Helper for Corollary 9.21: equip `H × ℝ` with the `ℓ²` product norm coming from
`WithLp 2 (H × ℝ)`. -/
local instance prod_normedAddCommGroup_l2_cor921 : NormedAddCommGroup (H × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) H ℝ

/-- Helper for Corollary 9.21: the `ℓ²` product norm is compatible with scalar multiplication on
`H × ℝ`. -/
local instance prod_normedSpace_l2_cor921 : NormedSpace ℝ (H × ℝ) := by
  letI : NormedAddCommGroup (H × ℝ) :=
    WithLp.normedAddCommGroupToProd (p := 2) H ℝ
  exact
    WithLp.normedSpaceSeminormedAddCommGroupToProd
      (p := 2) (α := H) (β := ℝ)

/-- Helper for Corollary 9.21: completeness of `H × ℝ` for the `ℓ²` product metric follows from
the uniform equivalence with `WithLp 2 (H × ℝ)`. -/
local instance prod_completeSpace_l2_cor921 : CompleteSpace (H × ℝ) := by
  letI : PseudoMetricSpace (H × ℝ) :=
    WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ
  exact (WithLp.uniformEquivProd (p := 2) H ℝ).completeSpace_iff.1 inferInstance

/-- Helper for Corollary 9.21: the product Hilbert structure on `H × ℝ` is the textbook one
`⟪(u, a), (v, b)⟫ = ⟪u, v⟫ + ab`. -/
local instance prod_innerProductSpace_l2_cor921 : InnerProductSpace ℝ (H × ℝ) where
  inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
  norm_sq_eq_re_inner x := by
    -- The `ℓ²` product norm is exactly the sum of the squared component norms.
    rw [show ‖x‖ = ‖WithLp.toLp 2 x‖ by rfl, WithLp.prod_norm_sq_eq_of_L2]
    simp [sq]
  conj_inner_symm x y := by
    -- Over `ℝ`, the componentwise formula is symmetric.
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    -- Bilinearity is inherited from the two component inner products.
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    -- Scalar multiplication distributes through both component contributions.
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

omit [CompleteSpace H] in
/-- Helper for Corollary 9.21: `Γ₀(H)` convexity on the effective domain is equivalent to
convexity of the real-height epigraph. -/
private theorem convex_epigraph_of_mem_gammaZero {f : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) :
    Convex ℝ (epigraph (fun y : H ↦ (f y : EReal))) := by
  -- Translate convexity on `effectiveDomain f` to the `dom` formulation used by the epigraph API.
  refine (convex_epigraph_iff_jensen_on_dom (fun y : H ↦ (f y : EReal))).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  simpa using hf.2.ineq hx' hy' hα hα_lt_one

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 9.21: every effective-domain point yields its canonical real-height
epigraph point at ordinate `(f y).toReal`. -/
private lemma mem_epigraph_toReal_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∈ effectiveDomain f) :
    (y, (f y : EReal).toReal) ∈ epigraph (fun z : H ↦ (f z : EReal)) := by
  -- Finiteness of `f y` exactly says that the `toReal` ordinate sits on or above the epigraph.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hy))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 9.21: a real-height epigraph point has base point in the effective
domain, and its ordinate dominates `(f y).toReal`. -/
private lemma effectiveDomain_and_toReal_le_of_mem_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph (fun z : H ↦ (f z : EReal))) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- A real ordinate is finite, so epigraph membership first forces `y` into the effective domain.
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
/-- Helper for Corollary 9.21: the product Hilbert inner product on `H × ℝ` splits into its
`H`-component and scalar component after translating by `(p, π)`. -/
private lemma inner_sub_prod_eq {x y p : H} {ξ η π : ℝ} :
    ⟪(y, η) - (p, π), (x, ξ) - (p, π)⟫_ℝ =
      ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) := rfl

/-- Helper for Corollary 9.21: the real-height epigraph of a `Γ₀(H)` function is a Chebyshev set
in the product Hilbert space `H × ℝ`. -/
private theorem isChebyshev_epigraph_of_mem_gammaZero {f : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) :
    IsChebyshev (epigraph (fun y : H ↦ (f y : EReal)) : Set (H × ℝ)) := by
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
    convex_epigraph_of_mem_gammaZero hf
  -- The Hilbert projection theorem applies to closed convex subsets of `H × ℝ`.
  exact isChebyshev_of_nonempty_isClosed_convex hnonempty hclosed hconv

/-- Helper for Corollary 9.21: the epigraph projection characterization yields the variational
inequality used to build an affine minorant. -/
private theorem
    eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero
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
      -- Testing the projection inequality at `(p, π + 1)` forces `ξ ≤ π`.
      change (f p : EReal) ≤ ((π + 1 : ℝ) : EReal)
      exact le_trans hp_le (by
        exact_mod_cast le_add_of_nonneg_right (show 0 ≤ (1 : ℝ) by norm_num))
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
    -- Evaluating the projection inequality at the canonical real-height epigraph point produces
    -- the desired domain-level variational inequality.
    simpa [C] using hproj_var (y, (f y : EReal).toReal) hyC
  · rintro ⟨hmax, hvar⟩
    have hp_mem : (p, π) ∈ C := by
      -- The max-bound already contains ordinary epigraph membership of `(p, π)`.
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
      -- Since `ξ - π ≤ 0`, increasing the height from `(f y).toReal` to `η` can only decrease
      -- the scalar contribution in the variational inequality.
      exact
        mul_le_mul_of_nonpos_right
          (sub_le_sub_right hfy_le_eta π) (sub_nonpos.mpr hξ_le)
    have hsum :
        ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) ≤
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hscalar ⟪y - p, x - p⟫_ℝ
    calc
      ⟪(y, η) - (p, π), (x, ξ) - (p, π)⟫_ℝ
          = ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) := inner_sub_prod_eq
      _ ≤ ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) := hsum
      _ ≤ 0 := hvar y hy

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 9.21: a real-height epigraph point projects to a point in the effective
domain because any real ordinate is strictly below `⊤`. -/
private theorem mem_effectiveDomain_of_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph (fun y : H ↦ (f y : EReal))) :
    x ∈ effectiveDomain f := by
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hxξ) (EReal.coe_lt_top _)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 9.21: outside the effective domain, the value of `f` must be `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∉ effectiveDomain f) :
    (f y : EReal) = ⊤ := by
  -- If the value were finite, it would put `y` back into the effective domain.
  by_contra htop
  exact hy (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

/-- Helper for Corollary 9.21: the projection inequality from the epigraph argument normalizes to
an affine lower support inequality on the effective domain. -/
private theorem affine_minorant_on_effectiveDomain_of_projection
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)) :
    let u : H := ((π - ξ)⁻¹) • (x - p)
    ∀ y ∈ effectiveDomain f,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  have hproj_data :
      max (ξ : EReal) (f p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain f,
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp hproj
  rcases hproj_data with ⟨hmax, hvar⟩
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point lies in the real-height epigraph.
    rw [hproj]
    exact
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  have hξ_le_pi : ξ ≤ π := by
    have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
      exact le_trans
        (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _)
        hmax
    exact_mod_cast hξ_le_pi'
  have hfp_top : (f p : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f p : EReal) > ⊥ from (f p).2)
  have hfp_le_pi : (f p : EReal).toReal ≤ π := by
    -- Epigraph membership identifies `π` as a real upper bound for the finite value `f p`.
    have hfp_le_pi' : (f p : EReal) ≤ (π : EReal) :=
      mem_epigraph_iff _ _ _ |>.mp hp_mem_epigraph
    have hcast :
        (((f p : EReal).toReal : ℝ) : EReal) ≤ (π : EReal) := by
      simpa [EReal.coe_toReal hfp_top hfp_bot] using hfp_le_pi'
    exact_mod_cast hcast
  have hξ_lt_pi : ξ < π := by
    -- Equality `π = ξ` would force `x = p`, contradicting the choice of `ξ < f x`.
    by_cases hπξ : π = ξ
    · have hvarx :
        ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        simp
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hfp_le_xi : (f p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (f p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (f p : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hfx_le_xi : (f x : EReal).toReal ≤ ξ := by
        have hfx_top : (f x : EReal) ≠ ⊤ :=
          ne_of_lt (mem_effectiveDomain_iff.mp hx)
        have hfx_bot : (f x : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (f x : EReal) > ⊥ from (f x).2)
        have hfx_le_xi' : (f x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hfp_le_xi
        have hcast :
            (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hfx_top hfx_bot] using hfx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  dsimp
  intro y hy
  have hvar :
      ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    hvar y hy
  have hgap_pos : 0 < π - ξ := by
    -- The projection ordinate is strictly above the point chosen below the epigraph.
    exact sub_pos.mpr hξ_lt_pi
  have hinner_le :
      ⟪y - p, x - p⟫_ℝ ≤
        ((f y : EReal).toReal - π) * (π - ξ) := by
    -- Rewrite the variational inequality in terms of the positive gap `π - ξ`.
    nlinarith
  have hscaled :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ ≤
        (f y : EReal).toReal - π := by
    -- Divide by the positive gap to obtain the affine support slope.
    have hdiv : ⟪y - p, x - p⟫_ℝ / (π - ξ) ≤ (f y : EReal).toReal - π := by
      refine (div_le_iff₀ hgap_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
    simpa [div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hreal :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (f p : EReal).toReal ≤
        (f y : EReal).toReal := by
    -- Replace the intercept `π` by the smaller value `(f p).toReal`.
    linarith
  have hfy_top : (f y : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f y : EReal) > ⊥ from (f y).2)
  have hcast :
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ
          + (f p : EReal).toReal : ℝ) : EReal) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_toReal hfy_top hfy_bot] using hcast

/-- Helper for Corollary 9.21: every function in `Γ₀(H)` admits a continuous affine minorant of
the form `y ↦ ⟪y - p, u⟫ + f p`. -/
private theorem exists_affine_minorant_of_mem_gammaZero_local
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ p ∈ effectiveDomain f, ∃ u : H, ∀ y : H,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  -- Choose a point of the effective domain and move one unit strictly below the epigraph there.
  rcases hf.2.nonempty with ⟨x, hx⟩
  let ξ : ℝ := (f x : EReal).toReal - 1
  have hξ : ξ < (f x : EReal).toReal := by
    -- The chosen ordinate sits one unit below the finite value of `f x`.
    dsimp [ξ]
    linarith
  let z : H × ℝ :=
    projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  let p : H := z.1
  let π : ℝ := z.2
  have hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
    -- The chosen coordinates are exactly the components of the projection point.
    simp [p, π, z]
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point lands in the target epigraph.
    rw [hproj]
    exact
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  have hproj_data :
      max (ξ : EReal) (f p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain f,
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp hproj
  have hξ_lt_pi : ξ < π := by
    rcases hproj_data with ⟨hmax, hvar⟩
    have hξ_le_pi : ξ ≤ π := by
      have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
        exact le_trans
          (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _)
          hmax
      exact_mod_cast hξ_le_pi'
    by_cases hπξ : π = ξ
    · have hvarx :
          ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        simp
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hfp_le_xi : (f p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (f p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (f p : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hfx_top : (f x : EReal) ≠ ⊤ :=
        ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hfx_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (f x : EReal) > ⊥ from (f x).2)
      have hfx_le_xi : (f x : EReal).toReal ≤ ξ := by
        have hfx_le_xi' : (f x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hfp_le_xi
        have hcast :
            (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hfx_top hfx_bot] using hfx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  let u : H := ((π - ξ)⁻¹) • (x - p)
  refine ⟨p, hp, u, ?_⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · -- On the effective domain, the normalized projection inequality gives the affine support
    -- bound.
    simpa [u] using
      affine_minorant_on_effectiveDomain_of_projection hf hx hξ hproj y hy
  · -- Off the effective domain, the right-hand side is `⊤`, so the inequality is automatic.
    rw [value_eq_top_of_not_mem_effectiveDomain hy]
    exact
      (le_top :
        ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (⊤ : EReal))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 9.21: a bounded subset of a Hilbert space has a uniform norm bound on
its subtype points. -/
private theorem norm_le_radius_of_mem_bounded_subtype {C : Set H}
    (hC_bounded : Bornology.IsBounded C) :
    ∃ R : ℝ, ∀ x : C, ‖(x : H)‖ ≤ R := by
  -- Realize boundedness by containment in a closed ball centered at the origin.
  rcases hC_bounded.subset_closedBall (0 : H) with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  intro x
  -- Membership in that closed ball is exactly the desired norm estimate.
  have hx_ball : (x : H) ∈ Metric.closedBall (0 : H) R := hR x.2
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx_ball

omit [CompleteSpace H] in
/-- Helper for Corollary 9.21: once the subset has a uniform radius bound, any affine functional
of the form `x ↦ ⟪x - p, u⟫ + α` has a uniform lower bound on the subtype. -/
private theorem affine_minorant_lower_bound_on_bounded_subtype {C : Set H}
    (hC_radius : ∃ R : ℝ, ∀ x : C, ‖(x : H)‖ ≤ R) (p u : H) (α : ℝ) :
    ∃ m : ℝ, ∀ x : C, m ≤ ⟪(x : H) - p, u⟫_ℝ + α := by
  rcases hC_radius with ⟨R, hR⟩
  refine ⟨-((R + ‖p‖) * ‖u‖) + α, ?_⟩
  intro x
  -- Cauchy-Schwarz bounds the affine slope from below by the product of the norms.
  have hinner :
      -(‖(x : H) - p‖ * ‖u‖) ≤ ⟪(x : H) - p, u⟫_ℝ :=
    (abs_le.mp (abs_real_inner_le_norm ((x : H) - p) u)).1
  -- The bounded radius of `C` turns that pointwise norm into a uniform one.
  have hnorm_sub : ‖(x : H) - p‖ ≤ ‖(x : H)‖ + ‖p‖ := norm_sub_le _ _
  have hnorm_sub' : ‖(x : H) - p‖ ≤ R + ‖p‖ := by
    exact le_trans hnorm_sub (add_le_add (hR x) le_rfl)
  have hmul :
      ‖(x : H) - p‖ * ‖u‖ ≤ (R + ‖p‖) * ‖u‖ := by
    exact mul_le_mul_of_nonneg_right hnorm_sub' (norm_nonneg _)
  -- Combining the two inequalities yields one explicit lower bound for all `x ∈ C`.
  nlinarith

/-- Helper for Corollary 9.21: a real lower bound remains a lower bound after coercion to
`EReal`. -/
private theorem ereal_coe_lower_bound_of_real_lower_bound {a b : ℝ} (h : a ≤ b) :
    ((a : ℝ) : EReal) ≤ (b : EReal) := by
  exact_mod_cast h

-- Proof sketch: apply Theorem 9.20 to obtain an affine minorant `x ↦ ⟪x - p, u⟫ + f p` of `f`.
-- A bounded subset has uniformly bounded norms, so Cauchy-Schwarz yields a uniform lower bound for
-- that affine functional on the subset, hence also for `f`.
/-- Corollary 9.21: every `Γ₀(H)` function on a real Hilbert space is bounded below on every
bounded subset of `H`, hence in particular on every nonempty bounded subset. -/
theorem bddBelow_on_bounded_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H}
    (hC_bounded : Bornology.IsBounded C) :
    BddBelow (Set.range fun x : C ↦ (f x : EReal)) := by
  -- Theorem 9.20 supplies the global affine minorant that controls `f` from below.
  rcases exists_affine_minorant_of_mem_gammaZero_local hf with ⟨p, hp, u, hminorant⟩
  -- The bounded set contributes a single radius bound on all subtype points.
  have hC_radius : ∃ R : ℝ, ∀ x : C, ‖(x : H)‖ ≤ R :=
    norm_le_radius_of_mem_bounded_subtype hC_bounded
  -- That radius makes the affine minorant uniformly bounded below on `C`.
  rcases affine_minorant_lower_bound_on_bounded_subtype
      hC_radius p u (f p : EReal).toReal with ⟨m, hm⟩
  rw [bddBelow_iff_exists_le ((m : ℝ) : EReal)]
  refine ⟨(m : EReal), le_rfl, ?_⟩
  rintro z ⟨x, rfl⟩
  -- Cast the real lower bound to `EReal` and compose it with the affine minorant inequality.
  have hcast :
      ((m : ℝ) : EReal) ≤
        ((⟪(x : H) - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) :=
    ereal_coe_lower_bound_of_real_lower_bound (hm x)
  exact le_trans hcast (hminorant (x : H))

end

end ERealFunction
