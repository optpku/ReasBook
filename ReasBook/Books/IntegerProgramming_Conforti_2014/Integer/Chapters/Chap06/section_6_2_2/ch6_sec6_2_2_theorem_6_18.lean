/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.Recession
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_26
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free
import Mathlib.NumberTheory.WellApproximable

open Set
open MeasureTheory
open scoped IntegerVectorNotation
open scoped Matrix
open scoped Pointwise

section Theorem618

variable {p : ℕ}

/-- Helper for Theorem 6.18: a full-dimensional maximal lattice-free set has nonempty interior. -/
lemma maximalLatticeFreeInteriorNonempty
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    (interior K).Nonempty := by
  -- Full dimensionality upgrades convexity to nonempty interior.
  exact
    (Convex.interior_nonempty_iff_affineSpan_eq_top
      (is_maximal_lattice_free.convex hK)).2 hfull

/-- Helper for Theorem 6.18: every lineality direction is automatically a recession direction. -/
lemma mem_recessionCone_of_mem_linealitySpace
    {K : Set (Fin p → ℝ)}
    {r : Fin p → ℝ}
    (hr : r ∈ linealitySpace K) :
    r ∈ recessionCone K := by
  -- The lineality condition allows translation by every scalar, hence by every nonnegative scalar.
  rw [mem_linealitySpace_iff] at hr
  rw [mem_recessionCone_iff]
  intro x hx a ha
  exact hr hx a

/-- Helper for Theorem 6.18: translating an interior point along a recession direction stays in
the interior. -/
lemma recessionDirectionPreservesInterior
    {K : Set (Fin p → ℝ)}
    {x₀ r : Fin p → ℝ}
    (hx₀ : x₀ ∈ interior K)
    (hr : r ∈ recessionCone K)
    {a : ℝ}
    (ha : 0 ≤ a) :
    x₀ + a • r ∈ interior K := by
  -- Translate an open neighborhood of `x₀` by the recession step.
  rw [mem_interior_iff_mem_nhds] at hx₀ ⊢
  rcases mem_nhds_iff.mp hx₀ with ⟨s, hsK, hsOpen, hx₀s⟩
  have hsImageOpen : IsOpen ((fun x : Fin p → ℝ ↦ x + a • r) '' s) := by
    exact (Homeomorph.addRight (a • r)).isOpenMap _ hsOpen
  have hsImageSubset : ((fun x : Fin p → ℝ ↦ x + a • r) '' s) ⊆ K := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (mem_recessionCone_iff.mp hr) (hsK hx) a ha
  have hx₀Image : x₀ + a • r ∈ (fun x : Fin p → ℝ ↦ x + a • r) '' s := by
    exact ⟨x₀, hx₀s, rfl⟩
  exact Filter.mem_of_superset (hsImageOpen.mem_nhds hx₀Image) hsImageSubset

/-- Helper for Theorem 6.18: if a recession direction is not in the lineality space, then some
point of `K` leaves `K` after a positive backward step along that direction. -/
lemma existsBackwardEscapeOf_mem_recessionCone_of_not_mem_linealitySpace
    {K : Set (Fin p → ℝ)}
    {r : Fin p → ℝ}
    (hr : r ∈ recessionCone K)
    (hnot : r ∉ linealitySpace K) :
    ∃ y ∈ K, ∃ t : ℝ, 0 < t ∧ y - t • r ∉ K := by
  -- Negating the lineality condition yields a violating translate; recession forces it to be a
  -- negative translate, which we rewrite as a positive backward step.
  rw [mem_linealitySpace_iff] at hnot
  push Not at hnot
  rcases hnot with ⟨y, hyK, a, hya⟩
  have ha_not_nonneg : ¬ 0 ≤ a := by
    intro ha
    exact hya ((mem_recessionCone_iff.mp hr) hyK a ha)
  have hneg : 0 < -a := neg_pos.mpr (lt_of_not_ge ha_not_nonneg)
  refine ⟨y, hyK, -a, hneg, ?_⟩
  simpa [sub_eq_add_neg, neg_smul] using hya

/-- Helper for Theorem 6.18: a full-dimensional maximal lattice-free set is closed. -/
lemma maximalLatticeFree_isClosed
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    IsClosed K := by
  -- Compare `K` with its closure; maximality forces equality once the closure stays lattice-free.
  have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
  have hinterior : (interior K).Nonempty := maximalLatticeFreeInteriorNonempty hfull hK
  have hclosureFree : is_lattice_free (closure K) := by
    -- The convex full-dimensional hypothesis identifies the interiors of `K` and `closure K`.
    rw [is_lattice_free_iff]
    intro z
    rw [hconv.interior_closure_eq_interior_of_nonempty_interior hinterior]
    exact (is_lattice_free_iff.mp (is_maximal_lattice_free.lattice_free hK)) z
  have hclosure_eq : closure K = K :=
    is_maximal_lattice_free.eq_of_subset hK subset_closure hconv.closure hclosureFree
  exact closure_eq_iff_isClosed.mp hclosure_eq

/-- Helper for Theorem 6.18: after moving slightly toward an interior point, a backward escape
may be arranged to start inside `interior K`. -/
lemma existsInteriorBackwardEscape
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K)
    {r : Fin p → ℝ}
    (hr : r ∈ recessionCone K)
    (hnot : r ∉ linealitySpace K) :
    ∃ x ∈ interior K, ∃ t : ℝ, 0 < t ∧ x - t • r ∉ K := by
  have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
  have hclosed : IsClosed K := maximalLatticeFree_isClosed hfull hK
  rcases maximalLatticeFreeInteriorNonempty hfull hK with ⟨x₀, hx₀⟩
  rcases existsBackwardEscapeOf_mem_recessionCone_of_not_mem_linealitySpace hr hnot with
    ⟨y, hyK, t, ht, hyOut⟩
  let z : Fin p → ℝ := y - t • r
  have hzOut : z ∉ K := hyOut
  let φ : ℝ → Fin p → ℝ := fun s ↦ (1 - s) • z + s • x₀
  have hφ_cont : Continuous φ := by
    continuity
  have hpreimage :
      φ ⁻¹' Kᶜ ∈ nhds (0 : ℝ) := by
    -- The complement of the closed set `K` is open, so points on the affine path stay outside
    -- for all sufficiently small positive parameters.
    have hzMem : z ∈ Kᶜ := hzOut
    have hφ0 : φ 0 ∈ Kᶜ := by
      simpa [φ, z] using hzMem
    exact hφ_cont.continuousAt.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hφ0)
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hεpos, hεsubset⟩
  let s : ℝ := min (ε / 2) (1 / 2)
  have hsPos : 0 < s := by
    dsimp [s]
    refine lt_min ?_ (by norm_num)
    linarith
  have hsLtOne : s < 1 := by
    have hsLe : s ≤ 1 / 2 := by
      dsimp [s]
      exact min_le_right _ _
    linarith
  have hsLtEps : s < ε := by
    have hsLe : s ≤ ε / 2 := by
      dsimp [s]
      exact min_le_left _ _
    linarith
  have hsBall : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hsPos.le]
    exact hsLtEps
  have hφsOut : φ s ∉ K := by
    have hsMem : s ∈ φ ⁻¹' Kᶜ := hεsubset hsBall
    simpa [Set.mem_preimage, φ] using hsMem
  have hxInterior : (1 - s) • y + s • x₀ ∈ interior K := by
    -- A positive convex combination of a point in `K` and an interior point lies in `interior K`.
    exact hconv.combo_self_interior_mem_interior hyK hx₀ (sub_nonneg.mpr hsLtOne.le) hsPos
      (sub_add_cancel 1 s)
  refine ⟨(1 - s) • y + s • x₀, hxInterior, (1 - s) * t, ?_, ?_⟩
  · -- The new escape parameter stays positive because `s ∈ (0,1)`.
    exact mul_pos (sub_pos.mpr hsLtOne) ht
  · -- Rewriting the translated point onto the affine path reduces the claim to `hφsOut`.
    simpa [φ, z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, sub_smul, smul_add,
      mul_smul] using hφsOut

/-- Helper for Theorem 6.18: a backward ray from an interior point to an outside point crosses the
frontier in between. -/
lemma backwardRayFrontierPoint
    {K : Set (Fin p → ℝ)}
    (hclosed : IsClosed K)
    {x r : Fin p → ℝ}
    (hx : x ∈ interior K)
    {t : ℝ}
    (ht : 0 < t)
    (hout : x - t • r ∉ K) :
    ∃ τ ∈ Ioo (0 : ℝ) t, x - τ • r ∈ frontier K := by
  let φ : ℝ → Fin p → ℝ := fun s ↦ x - s • r
  have hφ_cont : Continuous φ := by
    continuity
  let U : Set ℝ := φ ⁻¹' interior K
  let V : Set ℝ := φ ⁻¹' Kᶜ
  have hU_open : IsOpen U := by
    -- The interior branch is open because `φ` is continuous.
    dsimp [U]
    exact hφ_cont.isOpen_preimage _ isOpen_interior
  have hV_open : IsOpen V := by
    -- The complement branch is open because `K` is closed.
    dsimp [V]
    exact hφ_cont.isOpen_preimage _ hclosed.isOpen_compl
  have h0U : (0 : ℝ) ∈ U := by
    -- The ray starts in `interior K`.
    simpa [U, φ]
  have htV : t ∈ V := by
    -- The chosen escape time lands outside `K`.
    simpa [V, φ] using hout
  have hnot_cover : ¬ Icc (0 : ℝ) t ⊆ U ∪ V := by
    intro hcover
    -- If the whole interval split into the inside and outside branches, preconnectedness would
    -- force a point lying in both, contradicting `interior K ⊆ K`.
    have hpre := isPreconnected_Icc U V hU_open hV_open hcover
      ⟨0, left_mem_Icc.mpr ht.le, h0U⟩ ⟨t, right_mem_Icc.mpr ht.le, htV⟩
    rcases hpre with ⟨s, hsIcc, hsUV⟩
    exact hsUV.2 (interior_subset hsUV.1)
  rcases not_subset.mp hnot_cover with ⟨τ, hτIcc, hτnot⟩
  have hτ_not_interior : φ τ ∉ interior K := by
    -- The witness `τ` was chosen outside the interior branch.
    intro hmem
    exact hτnot (Or.inl (by simpa [U] using hmem))
  have hτ_mem : φ τ ∈ K := by
    -- The same witness also avoids the outside branch, so it still belongs to `K`.
    by_contra hmem
    exact hτnot (Or.inr (by simpa [V] using hmem))
  have hτ_ne_zero : τ ≠ 0 := by
    -- The endpoint `0` belongs to the inside branch, so `τ` cannot equal it.
    intro hτ0
    have : τ ∈ U := by
      simpa [hτ0] using h0U
    exact hτnot (Or.inl this)
  have hτ_ne_t : τ ≠ t := by
    -- The endpoint `t` belongs to the outside branch, so `τ` cannot equal it either.
    intro hτt
    have : τ ∈ V := by
      simpa [hτt] using htV
    exact hτnot (Or.inr this)
  refine ⟨τ, ⟨lt_of_le_of_ne hτIcc.1 (Ne.symm hτ_ne_zero),
    lt_of_le_of_ne hτIcc.2 hτ_ne_t⟩, ?_⟩
  -- Membership in the frontier is exactly the combination of `φ τ ∈ K` and `φ τ ∉ interior K`.
  exact (mem_frontier_iff_notMem_interior hτ_mem).2 hτ_not_interior

/-- Helper for Theorem 6.18: along a convex backward escape ray, there is a last parameter that
still lies in `K`, and every later parameter up to the escape time is already outside. -/
lemma backwardRayFirstExit
    {K : Set (Fin p → ℝ)}
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    {x r : Fin p → ℝ}
    (hx : x ∈ interior K)
    {t : ℝ}
    (ht : 0 < t)
    (hout : x - t • r ∉ K) :
    ∃ τ ∈ Ioo (0 : ℝ) t, x - τ • r ∈ frontier K ∧
      (∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∈ K) ∧
      (∀ s ∈ Ioc τ t, x - s • r ∉ K) := by
  let φ : ℝ → Fin p → ℝ := fun s ↦ x - s • r
  let S : Set ℝ := Icc (0 : ℝ) t ∩ φ ⁻¹' K
  have hφ_cont : Continuous φ := by
    continuity
  have hS_closed : IsClosed S := by
    -- The feasible scalar set is the intersection of a compact interval with the closed preimage.
    dsimp [S]
    exact isClosed_Icc.inter (hclosed.preimage hφ_cont)
  have hS_nonempty : S.Nonempty := by
    -- The interior start point gives the initial feasible parameter `0`.
    refine ⟨0, ?_⟩
    constructor
    · exact left_mem_Icc.mpr ht.le
    · simpa [φ] using interior_subset hx
  have hS_bdd : BddAbove S := by
    refine ⟨t, ?_⟩
    intro s hs
    exact hs.1.2
  let τ : ℝ := sSup S
  have hτ_mem : τ ∈ S := hS_closed.csSup_mem hS_nonempty hS_bdd
  have hτ_nonneg : 0 ≤ τ := hτ_mem.1.1
  have hτ_le_t : τ ≤ t := hτ_mem.1.2
  have hτ_mem_K : φ τ ∈ K := hτ_mem.2
  have hτ_lt_t : τ < t := by
    -- If the supremum reached `t`, then the outside endpoint would still lie in `K`.
    by_contra hτ_ge_t
    have hτ_eq_t : τ = t := le_antisymm hτ_le_t (le_of_not_gt hτ_ge_t)
    exact hout (by simpa [φ, hτ_eq_t] using hτ_mem_K)
  have hτ_not_interior : φ τ ∉ interior K := by
    intro hτ_int
    -- A small interval of interior points after `τ` would contradict the supremum property.
    have hpre :
        φ ⁻¹' interior K ∈ nhds τ := by
      exact hφ_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hτ_int)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hball⟩
    let d : ℝ := min (ε / 2) ((t - τ) / 2)
    have hd_pos : 0 < d := by
      dsimp [d]
      refine lt_min ?_ ?_
      · linarith
      · linarith
    have hd_lt_eps : d < ε := by
      have hd_le : d ≤ ε / 2 := by
        dsimp [d]
        exact min_le_left _ _
      linarith
    have hd_lt_gap : d < t - τ := by
      have hd_le : d ≤ (t - τ) / 2 := by
        dsimp [d]
        exact min_le_right _ _
      linarith
    let σ : ℝ := τ + d
    have hσ_lt_t : σ < t := by
      dsimp [σ]
      linarith
    have hσ_mem_ball : σ ∈ Metric.ball τ ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hσ_sub : σ - τ = d := by
        dsimp [σ]
        ring
      calc
        |σ - τ| = d := by rw [hσ_sub, abs_of_pos hd_pos]
        _ < ε := hd_lt_eps
    have hσ_mem_interior : φ σ ∈ interior K := by
      have hσ_pre : σ ∈ φ ⁻¹' interior K := hball hσ_mem_ball
      simpa [Set.mem_preimage] using hσ_pre
    have hσ_nonneg : 0 ≤ σ := by
      dsimp [σ]
      linarith
    have hσ_mem_S : σ ∈ S := by
      constructor
      · exact ⟨hσ_nonneg, hσ_lt_t.le⟩
      · simpa [Set.mem_preimage] using interior_subset hσ_mem_interior
    have hσ_le_τ : σ ≤ τ := le_csSup hS_bdd hσ_mem_S
    dsimp [σ] at hσ_le_τ
    linarith
  have hτ_pos : 0 < τ := by
    -- If the exit parameter were `0`, the starting interior point would already be on the frontier.
    by_contra hτ_nonpos
    have hτ_eq_zero : τ = 0 := le_antisymm (le_of_not_gt hτ_nonpos) hτ_nonneg
    exact hτ_not_interior (by simpa [φ, hτ_eq_zero] using hx)
  have hτ_frontier : φ τ ∈ frontier K := by
    -- The first-exit point lies in `K` but no longer in its interior.
    exact (mem_frontier_iff_notMem_interior hτ_mem_K).2 hτ_not_interior
  have hinside :
      ∀ s ∈ Icc (0 : ℝ) τ, φ s ∈ K := by
    intro s hs
    -- Convexity keeps the whole initial segment from `x` to the first-exit point inside `K`.
    have hxK : x ∈ K := interior_subset hx
    have hs_div_nonneg : 0 ≤ s / τ := by
      exact div_nonneg hs.1 hτ_pos.le
    have hs_div_le_one : s / τ ≤ 1 := by
      have hs_div_self : s / τ ≤ τ / τ := by
        exact div_le_div_of_nonneg_right hs.2 hτ_pos.le
      simpa [ne_of_gt hτ_pos] using hs_div_self
    have hleft_nonneg : 0 ≤ 1 - s / τ := sub_nonneg.mpr hs_div_le_one
    have hsum : (1 - s / τ) + (s / τ) = 1 := by ring
    have hcombo :
        (1 - s / τ) • x + (s / τ) • φ τ ∈ K := by
      exact hconv hxK hτ_mem_K hleft_nonneg hs_div_nonneg hsum
    have hφ_eq : φ s = (1 - s / τ) • x + (s / τ) • φ τ := by
      ext i
      have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
      change x i - s * r i = (1 - s / τ) * x i + (s / τ) * (x i - τ * r i)
      field_simp [hτ_ne]
      ring
    simpa [hφ_eq] using hcombo
  have houtside :
      ∀ s ∈ Ioc τ t, φ s ∉ K := by
    intro s hs hsK
    -- Any later scalar in `K` would violate the maximality of `τ` as the last feasible time.
    have hs_mem_S : s ∈ S := by
      constructor
      · exact ⟨le_trans hτ_pos.le hs.1.le, hs.2⟩
      · exact hsK
    have hs_le : s ≤ τ := le_csSup hS_bdd hs_mem_S
    exact (not_lt_of_ge hs_le) hs.1
  refine ⟨τ, ⟨hτ_pos, hτ_lt_t⟩, ?_, ?_, ?_⟩
  · simpa [φ] using hτ_frontier
  · intro s hs
    simpa [φ] using hinside s hs
  · intro s hs
    simpa [φ] using houtside s hs

/-- Helper for Theorem 6.18: Hahn-Banach separates a closed convex set from a point outside it. -/
lemma separatingFunctionalAtOutsideRayPoint
    {K : Set (Fin p → ℝ)}
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    {y : Fin p → ℝ}
    (hyK : y ∉ K) :
    ∃ f : (Fin p → ℝ) →L[ℝ] ℝ, ∃ c : ℝ,
      (∀ z ∈ K, f z ≤ c) ∧ c < f y := by
  -- Package the separation theorem in the exact shape needed for the later cap construction.
  obtain ⟨f, c, hsep, hysep⟩ :=
    geometric_hahn_banach_closed_point (s := K) (x := y) hconv hclosed hyK
  exact ⟨f, c, fun z hz ↦ le_of_lt (hsep z hz), hysep⟩

/-- Helper for Theorem 6.18: the coordinate strip between two consecutive integers around `a`
contains exactly the points whose `i`-th coordinate stays in that open unit interval. -/
def coordinateUnitStrip (i : Fin p) (a : ℝ) : Set (Fin p → ℝ) :=
  {u | (Int.floor a : ℝ) < u i ∧ u i < (Int.floor a : ℝ) + 1}

/-- Helper for Theorem 6.18: a coordinate unit strip is open. -/
lemma isOpen_coordinateUnitStrip
    (i : Fin p)
    (a : ℝ) :
    IsOpen (coordinateUnitStrip i a) := by
  -- The strip is cut out by two strict coordinate inequalities.
  dsimp [coordinateUnitStrip]
  exact
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

/-- Helper for Theorem 6.18: shifting one step farther along the backward ray subtracts
`δ * r i` from the `i`-th coordinate. -/
lemma rayShiftCoord_eq
    {x r : Fin p → ℝ}
    (τ δ : ℝ)
    (i : Fin p) :
    (x - (τ + δ) • r) i = (x - τ • r) i - δ * r i := by
  -- Normalize the coordinate arithmetic once so later slab arguments can reuse it verbatim.
  simp [Pi.sub_apply, Pi.smul_apply]
  ring

/-- Helper for Theorem 6.18: a coordinate unit strip is convex. -/
lemma convex_coordinateUnitStrip
    (i : Fin p)
    (a : ℝ) :
    Convex ℝ (coordinateUnitStrip i a) := by
  -- Convex combinations preserve the two strict coordinate bounds.
  intro x hx y hy α β hα hβ hαβ
  dsimp [coordinateUnitStrip] at hx hy ⊢
  constructor
  · -- The lower strip bound is preserved coordinatewise by the convex combination.
    by_cases hαzero : α = 0
    · have hβone : β = 1 := by linarith
      simpa [Pi.add_apply, Pi.smul_apply, hαzero, hβone] using hy.1
    · have hαpos : 0 < α := lt_of_le_of_ne hα (by simpa [eq_comm] using hαzero)
      have hαlt : α * (Int.floor a : ℝ) < α * x i := by
        exact mul_lt_mul_of_pos_left hx.1 hαpos
      have hβle : β * (Int.floor a : ℝ) ≤ β * y i := by
        exact mul_le_mul_of_nonneg_left hy.1.le hβ
      calc
        (Int.floor a : ℝ)
            = α * (Int.floor a : ℝ) + β * (Int.floor a : ℝ) := by
                calc
                  (Int.floor a : ℝ) = (α + β) * (Int.floor a : ℝ) := by
                    rw [hαβ, one_mul]
                  _ = α * (Int.floor a : ℝ) + β * (Int.floor a : ℝ) := by
                    ring
        _ < α * x i + β * y i := add_lt_add_of_lt_of_le hαlt hβle
  · -- The upper strip bound is preserved by the same convexity calculation.
    by_cases hαzero : α = 0
    · have hβone : β = 1 := by linarith
      simpa [Pi.add_apply, Pi.smul_apply, hαzero, hβone] using hy.2
    · have hαpos : 0 < α := lt_of_le_of_ne hα (by simpa [eq_comm] using hαzero)
      have hαlt : α * x i < α * ((Int.floor a : ℝ) + 1) := by
        exact mul_lt_mul_of_pos_left hx.2 hαpos
      have hβle : β * y i ≤ β * ((Int.floor a : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left hy.2.le hβ
      calc
        α * x i + β * y i
            < α * ((Int.floor a : ℝ) + 1) + β * ((Int.floor a : ℝ) + 1) :=
                add_lt_add_of_lt_of_le hαlt hβle
        _ = (Int.floor a : ℝ) + 1 := by
              calc
                α * ((Int.floor a : ℝ) + 1) + β * ((Int.floor a : ℝ) + 1)
                    = (α + β) * ((Int.floor a : ℝ) + 1) := by
                        ring
                _ = (Int.floor a : ℝ) + 1 := by rw [hαβ, one_mul]

/-- Helper for Theorem 6.18: a coordinate unit strip is disjoint from the embedded integer
lattice. -/
lemma coordinateUnitStrip_disjoint_integerVectors
    (i : Fin p)
    (a : ℝ) :
    Disjoint (coordinateUnitStrip i a) (ℤ^p) := by
  -- Any integer vector has an integral `i`-th coordinate, but the strip keeps that coordinate
  -- strictly between two consecutive integers.
  rw [disjoint_left]
  intro u hu huint
  rw [mem_integerVectors_iff_forall] at huint
  rcases huint i with ⟨z, hz⟩
  have hlower : (Int.floor a : ℝ) < (z : ℝ) := by
    simpa [hz] using hu.1
  have hupper : (z : ℝ) < (Int.floor a : ℝ) + 1 := by
    simpa [hz] using hu.2
  have hsucc : Int.floor a + 1 ≤ z := Int.add_one_le_iff.mpr (by exact_mod_cast hlower)
  have hsucc_real : ((Int.floor a : ℝ) + 1) ≤ (z : ℝ) := by
    exact_mod_cast hsucc
  exact (not_le_of_gt hupper) hsucc_real

/-- Helper for Theorem 6.18: the first-exit point can be pushed slightly farther along the
backward ray to an outside point lying in an open convex coordinate strip disjoint from `ℤ^p`. -/
lemma existsOutsideRayPointWithCoordinateSlab
    {K : Set (Fin p → ℝ)}
    {x r : Fin p → ℝ}
    {t τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) t)
    (houtside : ∀ s ∈ Ioc τ t, x - s • r ∉ K)
    (hnot : r ∉ linealitySpace K) :
    ∃ i : Fin p, ∃ δ : ℝ, ∃ y : Fin p → ℝ,
      0 < δ ∧ τ + δ < t ∧ y = x - (τ + δ) • r ∧ y ∉ K ∧
        IsOpen (coordinateUnitStrip i (y i)) ∧
          Convex ℝ (coordinateUnitStrip i (y i)) ∧
            y ∈ coordinateUnitStrip i (y i) ∧
              Disjoint (coordinateUnitStrip i (y i)) (ℤ^p) ∧
                (x - τ • r ∈ coordinateUnitStrip i (y i) ∨
                  ((x - τ • r) i ∈ Set.range (Int.cast : ℤ → ℝ) ∧
                    ∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∉ coordinateUnitStrip i (y i))) := by
  -- Route correction: the arithmetic bridge is now an explicit coordinate strip, so the remaining
  -- theorem-local blocker is only the exposed-face localization step.
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    apply hnot
    simpa [hr0] using (zero_mem_linealitySpace : (0 : Fin p → ℝ) ∈ linealitySpace K)
  have hcoord : ∃ i : Fin p, r i ≠ 0 := by
    classical
    by_contra hcoord
    push Not at hcoord
    apply hr_ne_zero
    ext i
    exact hcoord i
  rcases hcoord with ⟨i, hri⟩
  let b : Fin p → ℝ := x - τ • r
  by_cases hbi_int : b i ∈ Set.range (Int.cast : ℤ → ℝ)
  · rcases hbi_int with ⟨m, hm⟩
    let δ : ℝ := min ((t - τ) / 2) (1 / (2 * |r i|))
    let y : Fin p → ℝ := x - (τ + δ) • r
    let U : Set (Fin p → ℝ) := coordinateUnitStrip i (y i)
    have hδ_pos : 0 < δ := by
      -- The two candidate step sizes are both positive.
      dsimp [δ]
      refine lt_min ?_ ?_
      · linarith [hτ.2]
      · have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
        positivity
    have hτδ_lt_t : τ + δ < t := by
      -- Choosing `δ ≤ (t - τ) / 2` keeps the new point strictly before `t`.
      have hδ_le : δ ≤ (t - τ) / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      linarith
    have hy_out : y ∉ K := by
      -- The first-exit data already says every later parameter stays outside.
      apply houtside (τ + δ)
      exact ⟨by linarith, hτδ_lt_t.le⟩
    have hdelta_mul_abs_lt_one : |δ * r i| < 1 := by
      -- The second branch of the minimum bounds the coordinate shift by `1 / 2`.
      have hδ_le : δ ≤ 1 / (2 * |r i|) := by
        dsimp [δ]
        exact min_le_right _ _
      have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
      have hδ_nonneg : 0 ≤ δ := hδ_pos.le
      have hmul_le_half : |δ * r i| ≤ 1 / 2 := by
        calc
          |δ * r i| = δ * |r i| := by
            rw [abs_mul, abs_of_nonneg hδ_nonneg]
          _ ≤ (1 / (2 * |r i|)) * |r i| := by
            gcongr
          _ = 1 / 2 := by
            field_simp [ne_of_gt hri_abs_pos]
      linarith
    have hyi_not_int : y i ∉ Set.range (Int.cast : ℤ → ℝ) := by
      intro hyi_int
      rcases hyi_int with ⟨n, hn⟩
      have hyi_eq : y i = (m : ℝ) - δ * r i := by
        simpa [b, hm] using (rayShiftCoord_eq (x := x) (r := r) τ δ i)
      have hshift_ne : δ * r i ≠ 0 := mul_ne_zero (ne_of_gt hδ_pos) hri
      have hshift_sign : 0 < δ * r i ∨ δ * r i < 0 := lt_or_gt_of_ne hshift_ne.symm
      cases hshift_sign with
      | inl hshift_pos =>
          have hshift_lt_one : δ * r i < 1 := by
            exact (abs_lt.mp hdelta_mul_abs_lt_one).2
          have hy_upper : (n : ℝ) < (m : ℝ) := by
            linarith [hyi_eq, hn, hshift_pos]
          have hy_lower : (m : ℝ) - 1 < (n : ℝ) := by
            linarith [hyi_eq, hn, hshift_lt_one]
          have hm_le_n : m ≤ n := by
            have hm_lt_n_succ : m < n + 1 := by
              have hm_sub_lt_n : m - 1 < n := by
                exact_mod_cast hy_lower
              linarith
            exact Int.lt_add_one_iff.mp hm_lt_n_succ
          have hn_lt_m : n < m := by
            exact_mod_cast hy_upper
          exact (not_le_of_gt hn_lt_m) hm_le_n
      | inr hshift_neg =>
          have hneg_lt_shift : -1 < δ * r i := by
            exact (abs_lt.mp hdelta_mul_abs_lt_one).1
          have hy_lower : (m : ℝ) < (n : ℝ) := by
            linarith [hyi_eq, hn, hshift_neg]
          have hy_upper : (n : ℝ) < (m : ℝ) + 1 := by
            linarith [hyi_eq, hn, hneg_lt_shift]
          have hm_succ_le_n : m + 1 ≤ n := by
            exact Int.add_one_le_iff.mpr (by exact_mod_cast hy_lower)
          have hn_lt_succ : n < m + 1 := by
            exact_mod_cast hy_upper
          exact (not_le_of_gt hn_lt_succ) hm_succ_le_n
    have hy_mem : y ∈ U := by
      -- Once the chosen coordinate of `y` is nonintegral, it lies in its own unit strip.
      dsimp [U, coordinateUnitStrip]
      constructor
      · simpa using (Int.floor_lt_self_iff.2 hyi_not_int)
      · exact Int.lt_floor_add_one (y i)
    have hmiss_before_exit :
        ∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∉ U := by
      intro s hs hsU
      have hs_coord :
          (x - s • r) i = (m : ℝ) + (τ - s) * r i := by
        have hs_eq : x - s • r = b + (τ - s) • r := by
          ext j
          simp [b]
          ring
        have hs_eq_i := congrArg (fun z : Fin p → ℝ ↦ z i) hs_eq
        simpa [hm, Pi.add_apply, Pi.smul_apply] using hs_eq_i
      have hs_gap_nonneg : 0 ≤ τ - s := sub_nonneg.mpr hs.2
      have hyi_eq : y i = (m : ℝ) - δ * r i := by
        simpa [b, hm] using (rayShiftCoord_eq (x := x) (r := r) τ δ i)
      have hshift_ne : δ * r i ≠ 0 := mul_ne_zero (ne_of_gt hδ_pos) hri
      cases lt_or_gt_of_ne hshift_ne.symm with
      | inl hshift_pos =>
          have hri_pos : 0 < r i := by
            nlinarith [hshift_pos, hδ_pos]
          have hy_lower : (m : ℝ) - 1 ≤ y i := by
            have hshift_lt_one : δ * r i < 1 := (abs_lt.mp hdelta_mul_abs_lt_one).2
            linarith [hyi_eq, hshift_lt_one]
          have hy_upper : y i < (m : ℝ) := by
            linarith [hyi_eq, hshift_pos]
          have hfloor_y : Int.floor (y i) = m - 1 := by
            have hy_lower' : ((m - 1 : ℤ) : ℝ) ≤ y i := by
              simpa using hy_lower
            exact Int.floor_eq_iff.mpr ⟨hy_lower', by simpa using hy_upper⟩
          have hs_coord_ge : (m : ℝ) ≤ (x - s • r) i := by
            have hs_shift_nonneg : 0 ≤ (τ - s) * r i := mul_nonneg hs_gap_nonneg hri_pos.le
            linarith [hs_coord, hs_shift_nonneg]
          have hs_upper :
              (x - s • r) i < (Int.floor (y i) : ℝ) + 1 := by
            simpa [U, coordinateUnitStrip] using hsU.2
          rw [hfloor_y] at hs_upper
          have hs_upper' : (x - s • r) i < (m : ℝ) := by
            simpa using hs_upper
          exact (not_lt_of_ge hs_coord_ge) hs_upper'
      | inr hshift_neg =>
          have hri_neg : r i < 0 := by
            nlinarith [hshift_neg, hδ_pos]
          have hy_lower : (m : ℝ) ≤ y i := by
            linarith [hyi_eq, hshift_neg.le]
          have hy_upper : y i < (m : ℝ) + 1 := by
            have hshift_gt_neg_one : -1 < δ * r i := (abs_lt.mp hdelta_mul_abs_lt_one).1
            linarith [hyi_eq, hshift_gt_neg_one]
          have hfloor_y : Int.floor (y i) = m := by
            exact Int.floor_eq_iff.mpr ⟨hy_lower, by simpa using hy_upper⟩
          have hs_coord_le : (x - s • r) i ≤ (m : ℝ) := by
            have hs_shift_nonpos : (τ - s) * r i ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hs_gap_nonneg hri_neg.le
            linarith [hs_coord, hs_shift_nonpos]
          have hs_lower :
              (Int.floor (y i) : ℝ) < (x - s • r) i := by
            simpa [U, coordinateUnitStrip] using hsU.1
          rw [hfloor_y] at hs_lower
          exact (not_lt_of_ge hs_coord_le) hs_lower
    have hbCoord : b i ∈ Set.range (Int.cast : ℤ → ℝ) := ⟨m, hm⟩
    refine ⟨i, δ, y, hδ_pos, hτδ_lt_t, rfl, hy_out, ?_, ?_, hy_mem, ?_,
      Or.inr ⟨by simpa [b] using hbCoord, hmiss_before_exit⟩⟩
    · simpa [coordinateUnitStrip] using isOpen_coordinateUnitStrip i (y i)
    · simpa [coordinateUnitStrip] using convex_coordinateUnitStrip i (y i)
    · simpa [coordinateUnitStrip] using coordinateUnitStrip_disjoint_integerVectors i (y i)
  · let gap : ℝ := min (b i - (Int.floor (b i) : ℝ)) (((Int.floor (b i) : ℝ) + 1) - b i)
    let δ : ℝ := min ((t - τ) / 2) (gap / (2 * |r i|))
    let y : Fin p → ℝ := x - (τ + δ) • r
    let U : Set (Fin p → ℝ) := coordinateUnitStrip i (y i)
    have hgap_pos : 0 < gap := by
      -- Nonintegrality of `b i` gives positive distance to both neighboring integers.
      dsimp [gap]
      refine lt_min ?_ ?_
      · have hfloor_lt : (Int.floor (b i) : ℝ) < b i := by
          simpa using (Int.floor_lt_self_iff.2 hbi_int)
        exact sub_pos.mpr hfloor_lt
      · have hupper : b i < (Int.floor (b i) : ℝ) + 1 := Int.lt_floor_add_one (b i)
        exact sub_pos.mpr hupper
    have hδ_pos : 0 < δ := by
      -- The time window and the coordinate gap both allow a positive step.
      dsimp [δ]
      refine lt_min ?_ ?_
      · linarith [hτ.2]
      · have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
        positivity
    have hτδ_lt_t : τ + δ < t := by
      -- Choosing `δ ≤ (t - τ) / 2` again keeps the new point before `t`.
      have hδ_le : δ ≤ (t - τ) / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      linarith
    have hy_out : y ∉ K := by
      -- The pushed point still lies past the first exit.
      apply houtside (τ + δ)
      exact ⟨by linarith, hτδ_lt_t.le⟩
    have hdelta_mul_abs_lt_gap : |δ * r i| < gap := by
      -- The second branch of the minimum bounds the coordinate shift by `gap / 2`.
      have hδ_le : δ ≤ gap / (2 * |r i|) := by
        dsimp [δ]
        exact min_le_right _ _
      have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
      have hδ_nonneg : 0 ≤ δ := hδ_pos.le
      have hmul_le_half : |δ * r i| ≤ gap / 2 := by
        calc
          |δ * r i| = δ * |r i| := by
            rw [abs_mul, abs_of_nonneg hδ_nonneg]
          _ ≤ (gap / (2 * |r i|)) * |r i| := by
            gcongr
          _ = gap / 2 := by
            field_simp [ne_of_gt hri_abs_pos]
      linarith
    have hyi_not_int : y i ∉ Set.range (Int.cast : ℤ → ℝ) := by
      intro hyi_int
      rcases hyi_int with ⟨n, hn⟩
      have hyi_eq : y i = b i - δ * r i := by
        simpa [b] using (rayShiftCoord_eq (x := x) (r := r) τ δ i)
      have hshift_upper : δ * r i < gap := (abs_lt.mp hdelta_mul_abs_lt_gap).2
      have hshift_lower : -gap < δ * r i := (abs_lt.mp hdelta_mul_abs_lt_gap).1
      have hgap_left : gap ≤ b i - (Int.floor (b i) : ℝ) := by
        dsimp [gap]
        exact min_le_left _ _
      have hgap_right : gap ≤ ((Int.floor (b i) : ℝ) + 1) - b i := by
        dsimp [gap]
        exact min_le_right _ _
      have hy_lower : (Int.floor (b i) : ℝ) < (n : ℝ) := by
        have : δ * r i < b i - (Int.floor (b i) : ℝ) :=
          lt_of_lt_of_le hshift_upper hgap_left
        linarith [hyi_eq, hn]
      have hy_upper : (n : ℝ) < (Int.floor (b i) : ℝ) + 1 := by
        have : -(((Int.floor (b i) : ℝ) + 1) - b i) < δ * r i :=
          lt_of_le_of_lt (by linarith [hgap_right]) hshift_lower
        linarith [hyi_eq, hn]
      have hsucc : Int.floor (b i) + 1 ≤ n := Int.add_one_le_iff.mpr (by exact_mod_cast hy_lower)
      have hsucc_real : ((Int.floor (b i) : ℝ) + 1) ≤ (n : ℝ) := by
        exact_mod_cast hsucc
      exact (not_le_of_gt hy_upper) hsucc_real
    have hy_mem : y ∈ U := by
      -- The chosen outside point sits in the strip determined by its own nonintegral coordinate.
      dsimp [U, coordinateUnitStrip]
      constructor
      · simpa using (Int.floor_lt_self_iff.2 hyi_not_int)
      · exact Int.lt_floor_add_one (y i)
    have hyi_eq : y i = b i - δ * r i := by
      simpa [b] using (rayShiftCoord_eq (x := x) (r := r) τ δ i)
    have hy_between_floor :
        (Int.floor (b i) : ℝ) ≤ y i ∧ y i < (Int.floor (b i) : ℝ) + 1 := by
      constructor
      · have hshift_upper : δ * r i < b i - (Int.floor (b i) : ℝ) :=
          lt_of_lt_of_le (abs_lt.mp hdelta_mul_abs_lt_gap).2 (by dsimp [gap]; exact min_le_left _ _)
        linarith [hyi_eq, hshift_upper]
      · have hshift_lower :
            -(((Int.floor (b i) : ℝ) + 1) - b i) < δ * r i := by
          have hgap_right : gap ≤ ((Int.floor (b i) : ℝ) + 1) - b i := by
            dsimp [gap]
            exact min_le_right _ _
          linarith [(abs_lt.mp hdelta_mul_abs_lt_gap).1, hgap_right]
        linarith [hyi_eq, hshift_lower]
    have hfloor_y : Int.floor (y i) = Int.floor (b i) := by
      exact Int.floor_eq_iff.mpr hy_between_floor
    have hb_mem_strip : b ∈ U := by
      dsimp [U, coordinateUnitStrip]
      rw [hfloor_y]
      constructor
      · simpa using (Int.floor_lt_self_iff.2 hbi_int)
      · exact Int.lt_floor_add_one (b i)
    refine ⟨i, δ, y, hδ_pos, hτδ_lt_t, rfl, hy_out, ?_, ?_, hy_mem, ?_, Or.inl hb_mem_strip⟩
    · simpa [coordinateUnitStrip] using isOpen_coordinateUnitStrip i (y i)
    · simpa [coordinateUnitStrip] using convex_coordinateUnitStrip i (y i)
    · simpa [coordinateUnitStrip] using coordinateUnitStrip_disjoint_integerVectors i (y i)

/-- Helper for Theorem 6.18: the quotient-coordinate image is the bounded object needed for the
forward bounded replay once the recession cone collapses to lineality. -/
lemma linealityQuotientImage_bounded_of_recessionEqLineality
    {K : Set (Fin p → ℝ)}
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    (hrec : recessionCone K = linealitySpace K) :
    Bornology.IsBounded ((linealityQuotientCoordinateMap K) '' K) := by
  -- Route correction: isolate the quotient boundedness contradiction before replaying the bounded
  -- source argument, so the forward theorem does not mix quotient transport with polyhedrality.
  let π := linealityQuotientCoordinateMap K
  have hπ_surj : Function.Surjective π := by
    -- Quotient coordinates are the composite of two surjective linear equivalences.
    exact
      (Module.finBasis ℝ ((Fin p → ℝ) ⧸ linealitySubmodule K)).equivFun.surjective.comp
        (linealitySubmodule K).mkQ_surjective
  have hsaturated : π ⁻¹' (π '' K) = K := by
    -- Fibers of `π` differ by a lineality vector, and `K` is invariant under such translations.
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨y, hyK, hxy⟩
      have hdiffKer : x - y ∈ LinearMap.ker π := by
        rw [LinearMap.mem_ker]
        rw [map_sub, hxy, sub_self]
      have hdiffLin : x - y ∈ linealitySpace K := by
        rw [← mem_linealitySubmodule_iff, ← linealityQuotientCoordinateMap_ker K]
        exact hdiffKer
      have hxK := (mem_linealitySpace_iff.mp hdiffLin) hyK (1 : ℝ)
      simpa using hxK
    · intro x hxK
      exact ⟨x, hxK, rfl⟩
  have hπ_cont : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hπ_quotient : Topology.IsQuotientMap π :=
    (LinearMap.isOpenMap_of_finiteDimensional π hπ_surj).isQuotientMap hπ_cont hπ_surj
  have himageClosed : IsClosed (π '' K) := by
    -- Closedness descends through the quotient map because the preimage is exactly `K`.
    apply hπ_quotient.isCoinducing.isClosed_preimage.mp
    rwa [hsaturated]
  have himageConvex : Convex ℝ (π '' K) := hconv.linear_image π
  rw [closed_convex_isBounded_iff_not_containsRay himageClosed himageConvex]
  rintro ⟨q, d, hd_ne, hray⟩
  rcases hπ_surj q with ⟨x, hx⟩
  rcases hπ_surj d with ⟨r, hr⟩
  have hliftedRay : ∀ t : ℝ, 0 ≤ t → x + t • r ∈ K := by
    intro t ht
    rw [← hsaturated]
    have hmap : π (x + t • r) = q + t • d := by
      rw [map_add, map_smul, hx, hr]
    change π (x + t • r) ∈ π '' K
    rw [hmap]
    exact hray t ht
  have hrAsymptotic : r ∈ (asymptoticCone ℝ K : Set (Fin p → ℝ)) :=
    mem_asymptoticCone_of_forall_nonneg_add_smul_mem hliftedRay
  have hrRecession : r ∈ recessionCone K := by
    -- Closed convexity upgrades the lifted asymptotic ray to a recession direction from every
    -- base point of `K`.
    rw [mem_recessionCone_iff]
    intro y hyK t ht
    simpa [add_comm] using
      hconv.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hclosed ht hrAsymptotic hyK
  have hrLineality : r ∈ linealitySpace K := by
    rwa [← hrec]
  have hrKer : r ∈ LinearMap.ker π := by
    rw [linealityQuotientCoordinateMap_ker K, mem_linealitySubmodule_iff]
    exact hrLineality
  have hπr : π r = 0 := LinearMap.mem_ker.mp hrKer
  exact hd_ne (hr.symm.trans hπr)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
an interior recession direction lets a large floor-rounded translate enter the integer lattice. -/
lemma not_latticeFree_of_memInterior_recessionCone
    {K : Set (Fin p → ℝ)}
    {x r : Fin p → ℝ}
    (hx : x ∈ interior K)
    (hr : r ∈ interior (recessionCone K))
    (hfree : is_lattice_free K) :
    False := by
  -- A small ball around `r` remains in the recession cone.
  rw [mem_interior_iff_mem_nhds] at hr
  rcases Metric.mem_nhds_iff.mp hr with ⟨ε, hεPos, hεBall⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hεPos
  let M : ℝ := N + 1
  let y : Fin p → ℝ := x + M • r
  let z : Fin p → ℤ := fun i ↦ Int.floor (y i)
  let zReal : Fin p → ℝ := Int.cast ∘ z
  let q : Fin p → ℝ := fun i ↦ (zReal i - y i) / M
  have hMPos : 0 < M := by
    dsimp [M]
    positivity
  have hrqBall : r + q ∈ Metric.ball r ε := by
    -- Every floor error is smaller than one, so division by `M` puts all coordinates in the ball.
    rw [Metric.mem_ball, dist_pi_lt_iff hεPos]
    intro i
    have hfloorLe : zReal i ≤ y i := by
      exact_mod_cast Int.floor_le (y i)
    have hfloorLt : y i < zReal i + 1 := by
      change y i < (((Int.floor (y i) : ℤ) : ℝ) + 1)
      exact_mod_cast Int.lt_floor_add_one (y i)
    have habsLtOne : |zReal i - y i| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have habsLtInv : |(zReal i - y i) / M| < 1 / M := by
      rw [abs_div, abs_of_pos hMPos]
      exact div_lt_div_of_pos_right habsLtOne hMPos
    have hinvLt : 1 / M < ε := by
      simpa [M] using hN
    simpa [q, abs_div, abs_of_pos hMPos] using habsLtInv.trans hinvLt
  have hrq : r + q ∈ recessionCone K := hεBall hrqBall
  have hzRealEq : zReal = x + M • (r + q) := by
    -- The correction vector was chosen so that the translated point is exactly integral.
    ext i
    have hMq : M * q i = zReal i - y i := by
      dsimp [q]
      field_simp [hMPos.ne']
    calc
      zReal i = y i + M * q i := by linarith
      _ = x i + M * r i + M * q i := by simp [y]
      _ = (x + M • (r + q)) i := by simp [Pi.add_apply, smul_add, add_assoc]
  have hzInterior : zReal ∈ interior K := by
    have htranslate : x + M • (r + q) ∈ interior K :=
      recessionDirectionPreservesInterior hx hrq hMPos.le
    rw [hzRealEq]
    exact htranslate
  have hzInteger : zReal ∈ (ℤ^p : Set (Fin p → ℝ)) :=
    (mem_integerVectors_iff).2 ⟨z, rfl⟩
  exact (is_lattice_free.not_mem_interior hfree hzInteger) hzInterior

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the recession cone of a full-dimensional lattice-free set has empty ambient interior. -/
lemma latticeFree_recessionCone_interior_eq_empty
    {K : Set (Fin p → ℝ)}
    (hKInterior : (interior K).Nonempty)
    (hfree : is_lattice_free K) :
    interior (recessionCone K) = ∅ := by
  -- Any point of this interior would contradict lattice-freeness by the rounding lemma.
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  rcases hKInterior with ⟨x, hx⟩
  exact not_latticeFree_of_memInterior_recessionCone hx hr hfree

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean: the lineality quotient saturates a set under its defining translations. -/
lemma linealityQuotientImage_preimage_eq
    {K : Set (Fin p → ℝ)} :
    (linealityQuotientCoordinateMap K) ⁻¹' ((linealityQuotientCoordinateMap K) '' K) = K := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨y, hyK, hxy⟩
    have hdiffKer : x - y ∈ LinearMap.ker (linealityQuotientCoordinateMap K) := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    have hdiffLin : x - y ∈ linealitySpace K := by
      rw [← mem_linealitySubmodule_iff, ← linealityQuotientCoordinateMap_ker K]
      exact hdiffKer
    have hxK := (mem_linealitySpace_iff.mp hdiffLin) hyK (1 : ℝ)
    simpa using hxK
  · intro x hxK
    exact ⟨x, hxK, rfl⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean: the quotient image inherits closedness and convexity. -/
lemma linealityQuotientImage_interface
    {K : Set (Fin p → ℝ)}
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K) :
    Function.Surjective (linealityQuotientCoordinateMap K) ∧
      IsClosed ((linealityQuotientCoordinateMap K) '' K) ∧
      Convex ℝ ((linealityQuotientCoordinateMap K) '' K) := by
  let π := linealityQuotientCoordinateMap K
  have hπSurj : Function.Surjective π := by
    exact
      (Module.finBasis ℝ ((Fin p → ℝ) ⧸ linealitySubmodule K)).equivFun.surjective.comp
        (linealitySubmodule K).mkQ_surjective
  have hπCont : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hπQuotient : Topology.IsQuotientMap π :=
    (LinearMap.isOpenMap_of_finiteDimensional π hπSurj).isQuotientMap hπCont hπSurj
  have himageClosed : IsClosed (π '' K) := by
    apply hπQuotient.isCoinducing.isClosed_preimage.mp
    rw [linealityQuotientImage_preimage_eq]
    exact hclosed
  have hImageConvex : Convex ℝ (π '' K) := hconv.linear_image π
  exact ⟨hπSurj, himageClosed, hImageConvex⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the lineality-quotient image is full-dimensional and maximal-free for the projected integer
vectors. -/
lemma linealityQuotientImage_maximalProjectedIntegerFree
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    affineSpan ℝ ((linealityQuotientCoordinateMap K) '' K) = ⊤ ∧
      is_maximal_free_of
        ((linealityQuotientCoordinateMap K) '' (ℤ^p : Set (Fin p → ℝ)))
        ((linealityQuotientCoordinateMap K) '' K) := by
  let π := linealityQuotientCoordinateMap K
  have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
  have hclosed : IsClosed K := maximalLatticeFree_isClosed hfull hK
  rcases linealityQuotientImage_interface hconv hclosed with
    ⟨hπSurj, _himageClosed, hImageConvex⟩
  have hπOpen : IsOpenMap π := LinearMap.isOpenMap_of_finiteDimensional π hπSurj
  have hπCont : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hImageInterior : (interior (π '' K)).Nonempty := by
    -- The open image of the nonempty ambient interior lies inside the quotient image.
    rcases maximalLatticeFreeInteriorNonempty hfull hK with ⟨x, hx⟩
    refine ⟨π x, mem_interior.mpr ⟨π '' interior K, ?_, ?_, ?_⟩⟩
    · exact Set.image_mono interior_subset
    · exact hπOpen (interior K) isOpen_interior
    · exact ⟨x, hx, rfl⟩
  have hImageFull : affineSpan ℝ (π '' K) = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hImageConvex).mp hImageInterior
  have hImageFree : is_free_of (π '' (ℤ^p : Set (Fin p → ℝ))) (π '' K) := by
    -- Openness identifies the interior of the saturated preimage with `interior K`.
    rw [is_free_of_iff]
    intro q hqInteger hqInterior
    rcases hqInteger with ⟨z, hzInteger, rfl⟩
    have hzInteriorPreimage : z ∈ interior (π ⁻¹' (π '' K)) := by
      rw [← hπOpen.preimage_interior_eq_interior_preimage hπCont]
      exact hqInterior
    have hzInteriorK : z ∈ interior K := by
      rwa [linealityQuotientImage_preimage_eq] at hzInteriorPreimage
    exact
      (is_lattice_free.not_mem_interior (is_maximal_lattice_free.lattice_free hK) hzInteger)
        hzInteriorK
  have hImageMaximal : is_maximal_free_of (π '' (ℤ^p : Set (Fin p → ℝ))) (π '' K) := by
    -- Pull a projected free enlargement back to the ambient space and use maximality of `K`.
    refine (is_maximal_free_of_iff).mpr ⟨hImageConvex, hImageFree, ?_⟩
    intro L hImageSubset hLConvex hLFree
    have hPreimageSubset : K ⊆ π ⁻¹' L := by
      intro x hx
      exact hImageSubset ⟨x, hx, rfl⟩
    have hPreimageConvex : Convex ℝ (π ⁻¹' L) := hLConvex.linear_preimage π
    have hPreimageFree : is_lattice_free (π ⁻¹' L) := by
      rw [is_lattice_free, is_free_of_iff]
      intro z hzInteger hzInterior
      have hzImageInterior : π z ∈ interior L := by
        have hzInterior' : z ∈ π ⁻¹' interior L := by
          rw [hπOpen.preimage_interior_eq_interior_preimage hπCont]
          exact hzInterior
        exact hzInterior'
      have hzProjectedInteger : π z ∈ π '' (ℤ^p : Set (Fin p → ℝ)) :=
        ⟨z, hzInteger, rfl⟩
      exact (is_free_of.not_mem_interior hLFree hzProjectedInteger) hzImageInterior
    have hPreimageEq : π ⁻¹' L = K :=
      is_maximal_lattice_free.eq_of_subset hK hPreimageSubset hPreimageConvex hPreimageFree
    apply Set.Subset.antisymm
    · intro q hqL
      rcases hπSurj q with ⟨x, rfl⟩
      have hxPreimage : x ∈ π ⁻¹' L := hqL
      have hxK : x ∈ K := by rwa [hPreimageEq] at hxPreimage
      exact ⟨x, hxK, rfl⟩
    · exact hImageSubset
  exact ⟨hImageFull, hImageMaximal⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the inverse image of a polyhedron under a linear map is a polyhedron. -/
lemma isPolyhedron_preimage_linearMap
    {n q : ℕ}
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    {Q : Set (Fin q → ℝ)}
    (hQ : is_polyhedron Q) :
    is_polyhedron (f ⁻¹' Q) := by
  rcases (is_polyhedron_iff.mp hQ) with ⟨m, A, b, hQPresentation⟩
  refine (is_polyhedron_iff.mpr ⟨m, A * LinearMap.toMatrix' f, b, ?_⟩)
  -- Matrix multiplication composes the quotient map with every defining row of `Q`.
  rw [hQPresentation]
  ext x
  rw [mem_preimage, mem_polyhedron_le_set_iff, mem_polyhedron_le_set_iff,
    ← LinearMap.toMatrix'_mulVec f x, Matrix.mulVec_mulVec]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
polyhedrality of the lineality-quotient image lifts to the original saturated set. -/
lemma isPolyhedron_of_linealityQuotientImage_isPolyhedron
    {K : Set (Fin p → ℝ)}
    (hQ : is_polyhedron ((linealityQuotientCoordinateMap K) '' K)) :
    is_polyhedron K := by
  -- Pull back the quotient presentation and identify its saturated inverse image with `K`.
  rw [← linealityQuotientImage_preimage_eq (K := K)]
  exact isPolyhedron_preimage_linearMap (linealityQuotientCoordinateMap K) hQ

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a discrete additive subgroup meets every bounded set in only finitely many points. -/
lemma finite_inter_addSubgroup_of_isBounded_of_isDiscrete
    {q : ℕ}
    (S : AddSubgroup (Fin q → ℝ))
    (hS : IsDiscrete (S : Set (Fin q → ℝ)))
    {B : Set (Fin q → ℝ)}
    (hB : Bornology.IsBounded B) :
    (B ∩ (S : Set (Fin q → ℝ))).Finite := by
  -- Discreteness makes the subgroup inclusion proper; compactness of the bounded closure then
  -- leaves only finitely many subgroup elements over that closure.
  have hfinite :
      ((fun s : S ↦ (s : Fin q → ℝ)) ⁻¹' closure B).Finite :=
    tendsto_cofinite_cocompact_iff.mp
      (S.tendsto_coe_cofinite_of_discrete hS) (closure B) hB.isCompact_closure
  refine (hfinite.image fun s : S ↦ (s : Fin q → ℝ)).subset ?_
  intro x hx
  refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
  exact subset_closure hx.1

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
an additive subgroup of a normed group is discrete exactly when zero is isolated by a ball. -/
lemma addSubgroup_isDiscrete_iff_exists_ball
    {E : Type*}
    [NormedAddCommGroup E]
    (S : AddSubgroup E) :
    IsDiscrete (S : Set E) ↔
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : E) ε ∩ (S : Set E) = {0} := by
  constructor
  · intro hS
    rcases isOpen_inter_eq_singleton_of_mem_discrete hS S.zero_mem with
      ⟨U, hUOpen, hUInter⟩
    have hzeroU : (0 : E) ∈ U := by
      have hzeroInter : (0 : E) ∈ U ∩ (S : Set E) := by
        rw [hUInter]
        exact Set.mem_singleton 0
      exact hzeroInter.1
    rcases Metric.isOpen_iff.mp hUOpen 0 hzeroU with ⟨ε, hεPos, hball⟩
    refine ⟨ε, hεPos, Set.Subset.antisymm ?_ ?_⟩
    · intro x hx
      have hxInter : x ∈ U ∩ (S : Set E) := ⟨hball hx.1, hx.2⟩
      rwa [hUInter] at hxInter
    · intro x hx
      have hxZero : x = 0 := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨by simpa using hεPos, S.zero_mem⟩
  · rintro ⟨ε, hεPos, hball⟩
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro y hyS
    refine ⟨Metric.ball y ε, Metric.isOpen_ball, ?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      have hxyS : x - y ∈ S := S.sub_mem hx.2 hyS
      have hxyBall : x - y ∈ Metric.ball (0 : E) ε := by
        simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx.1
      have hxyZero : x - y = 0 := by
        have hxyInter : x - y ∈ Metric.ball (0 : E) ε ∩ (S : Set E) :=
          ⟨hxyBall, hxyS⟩
        rw [hball] at hxyInter
        exact Set.mem_singleton_iff.mp hxyInter
      exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hxyZero)
    · intro x hx
      have hxy : x = y := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨by simpa using hεPos, hyS⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a nondiscrete additive subgroup of a finite-dimensional real coordinate space has a nonzero real
line in its topological closure. -/
lemma line_mem_topologicalClosure_of_not_isDiscrete_addSubgroup
    {q : ℕ}
    (S : AddSubgroup (Fin q → ℝ))
    (hS : ¬ IsDiscrete (S : Set (Fin q → ℝ))) :
    ∃ r : Fin q → ℝ, ‖r‖ = 1 ∧
      ∀ t : ℝ, t • r ∈ S.topologicalClosure := by
  classical
  have hsmall :
      ∀ n : ℕ, ∃ g : Fin q → ℝ,
        g ∈ S ∧ g ≠ 0 ∧ ‖g‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hradius : 0 < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hnone
    push Not at hnone
    have hball :
        Metric.ball (0 : Fin q → ℝ) (1 / ((n : ℝ) + 1)) ∩
            (S : Set (Fin q → ℝ)) = {0} := by
      apply Set.Subset.antisymm
      · intro g hg
        have hgNorm : ‖g‖ < 1 / ((n : ℝ) + 1) := by
          simpa [Metric.mem_ball, dist_zero_right] using hg.1
        apply Set.mem_singleton_iff.mpr
        by_contra hgZero
        exact (not_lt_of_ge (hnone g hg.2 hgZero)) hgNorm
      · intro g hg
        have hgZero : g = 0 := Set.mem_singleton_iff.mp hg
        subst g
        exact ⟨by simpa using hradius, S.zero_mem⟩
    exact hS ((addSubgroup_isDiscrete_iff_exists_ball S).2
      ⟨1 / ((n : ℝ) + 1), hradius, hball⟩)
  choose g hgS hgNe hgSmall using hsmall
  let u : ℕ → Fin q → ℝ := fun n ↦ (‖g n‖)⁻¹ • g n
  have huSphere : ∀ n, u n ∈ Metric.sphere (0 : Fin q → ℝ) 1 := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right]
    simp [u, norm_smul, hgNe n]
  rcases (isCompact_sphere (0 : Fin q → ℝ) 1).tendsto_subseq huSphere with
    ⟨r, hrSphere, φ, hφMono, huLimit⟩
  have hrNorm : ‖r‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hrSphere
  refine ⟨r, hrNorm, ?_⟩
  intro t
  let a : ℕ → ℝ := fun n ↦
    ((Int.floor (t / ‖g (φ n)‖) : ℤ) : ℝ) * ‖g (φ n)‖
  have hgNormLimit :
      Filter.Tendsto (fun n ↦ ‖g (φ n)‖) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ norm_nonneg (g (φ n))) (fun n ↦ (hgSmall (φ n)).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφMono.tendsto_atTop
  have haLimit : Filter.Tendsto a Filter.atTop (nhds t) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases Metric.tendsto_atTop.mp hgNormLimit ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn ↦ ?_⟩
    have hnormDist : dist ‖g (φ n)‖ 0 < ε := hN n hn
    have hnormSmall : ‖g (φ n)‖ < ε := by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (g (φ n)))] using hnormDist
    have hnormPos : 0 < ‖g (φ n)‖ := norm_pos_iff.mpr (hgNe (φ n))
    have hnormNe : ‖g (φ n)‖ ≠ 0 := ne_of_gt hnormPos
    have hfloorLe :
        ((Int.floor (t / ‖g (φ n)‖) : ℤ) : ℝ) ≤
          t / ‖g (φ n)‖ := by
      exact_mod_cast Int.floor_le (t / ‖g (φ n)‖)
    have hltFloor :
        t / ‖g (φ n)‖ <
          ((Int.floor (t / ‖g (φ n)‖) : ℤ) : ℝ) + 1 := by
      exact_mod_cast Int.lt_floor_add_one (t / ‖g (φ n)‖)
    have haLe : a n ≤ t := by
      dsimp [a]
      calc
        ((Int.floor (t / ‖g (φ n)‖) : ℤ) : ℝ) * ‖g (φ n)‖ ≤
            (t / ‖g (φ n)‖) * ‖g (φ n)‖ :=
          mul_le_mul_of_nonneg_right hfloorLe hnormPos.le
        _ = t := div_mul_cancel₀ t hnormNe
    have htLt : t < a n + ‖g (φ n)‖ := by
      dsimp [a]
      have hmul := mul_lt_mul_of_pos_right hltFloor hnormPos
      rw [div_mul_cancel₀ t hnormNe] at hmul
      linarith
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr haLe)]
    linarith
  have hsmulLimit :
      Filter.Tendsto (fun n ↦ a n • u (φ n)) Filter.atTop (nhds (t • r)) :=
    haLimit.smul huLimit
  change t • r ∈ closure (S : Set (Fin q → ℝ))
  refine mem_closure_of_tendsto hsmulLimit (Filter.Eventually.of_forall fun n ↦ ?_)
  have hnormNe : ‖g (φ n)‖ ≠ 0 := norm_ne_zero_iff.mpr (hgNe (φ n))
  have hrewrite :
      a n • u (φ n) =
        (Int.floor (t / ‖g (φ n)‖) : ℤ) • g (φ n) := by
    dsimp [a, u]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hnormNe, mul_one,
      Int.cast_smul_eq_zsmul]
  rw [hrewrite]
  exact S.zsmul_mem (hgS (φ n)) _

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a bounded full-dimensional maximal-free set forces its forbidden additive subgroup to be
discrete. -/
lemma boundedMaximalFree_addSubgroup_isDiscrete
    {q : ℕ}
    (S : AddSubgroup (Fin q → ℝ))
    {Q : Set (Fin q → ℝ)}
    (hQBounded : Bornology.IsBounded Q)
    (hQInterior : (interior Q).Nonempty)
    (hQMaximal : is_maximal_free_of (S : Set (Fin q → ℝ)) Q) :
    IsDiscrete (S : Set (Fin q → ℝ)) := by
  by_contra hSDiscrete
  rcases line_mem_topologicalClosure_of_not_isDiscrete_addSubgroup S hSDiscrete with
    ⟨r, hrNorm, hrClosure⟩
  let V : Set (Fin q → ℝ) := (ℝ ∙ r : Submodule ℝ (Fin q → ℝ))
  let U : Set (Fin q → ℝ) := interior Q + V
  let D : Set (Fin q → ℝ) := closure U
  have hQConvex : Convex ℝ Q := is_maximal_free_of.convex hQMaximal
  have hUOpen : IsOpen U := by
    -- Adding the line to the open interior preserves openness.
    exact isOpen_interior.add_right
  have hVConvex : Convex ℝ V := by
    exact Submodule.convex _
  have hUConvex : Convex ℝ U := hQConvex.interior.add hVConvex
  have hUNonempty : U.Nonempty := by
    rcases hQInterior with ⟨x, hx⟩
    refine ⟨x, x, hx, 0, Submodule.zero_mem _, ?_⟩
    exact add_zero x
  have hInteriorD : interior D = U := by
    -- Convexity identifies the interior of the closure with the original open saturation.
    rw [show D = closure U by rfl]
    rw [hUConvex.interior_closure_eq_interior_of_nonempty_interior]
    · exact hUOpen.interior_eq
    · simpa [hUOpen.interior_eq] using hUNonempty
  have hQSubsetD : Q ⊆ D := by
    -- A full-dimensional convex set is the closure of its interior, which is contained in `U`.
    intro x hxQ
    have hxClosure : x ∈ closure (interior Q) := by
      rw [hQConvex.closure_interior_eq_closure_of_nonempty_interior hQInterior]
      exact subset_closure hxQ
    apply closure_mono _ hxClosure
    intro y hy
    refine ⟨y, hy, 0, Submodule.zero_mem _, ?_⟩
    exact add_zero y
  have hDFree : is_free_of (S : Set (Fin q → ℝ)) D := by
    rw [is_free_of_iff]
    intro s hsS hsD
    rw [hInteriorD] at hsD
    rcases hsD with ⟨x, hxQ, v, hvV, hsv⟩
    rcases Submodule.mem_span_singleton.mp hvV with ⟨t, ht⟩
    have hsv' : s = x + t • r := by
      calc
        s = x + v := hsv.symm
        _ = x + t • r := by rw [ht]
    let W : Set (Fin q → ℝ) := (fun w ↦ s - w) ⁻¹' interior Q
    have hWOpen : IsOpen W := by
      exact isOpen_interior.preimage (continuous_const.sub continuous_id)
    have htrW : t • r ∈ W := by
      dsimp [W]
      rw [hsv']
      simpa using hxQ
    rcases (mem_closure_iff.mp (hrClosure t) W hWOpen htrW) with ⟨w, hwW, hwS⟩
    have hswS : s - w ∈ S := S.sub_mem hsS hwS
    exact (is_free_of.not_mem_interior (is_maximal_free_of.free hQMaximal) hswS) hwW
  have hDConvex : Convex ℝ D := hUConvex.closure
  have hDQ : D = Q := is_maximal_free_of.eq_of_subset hQMaximal hQSubsetD hDConvex hDFree
  rcases hQBounded.exists_norm_le with ⟨C, hC⟩
  rcases hQInterior with ⟨x, hx⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (C + ‖x‖)
  have hxnrU : x + (n : ℝ) • r ∈ U := by
    refine ⟨x, hx, (n : ℝ) • r,
      Submodule.smul_mem _ (n : ℝ) (Submodule.mem_span_singleton_self r), rfl⟩
  have hxnrQ : x + (n : ℝ) • r ∈ Q := by
    rw [← hDQ]
    exact subset_closure hxnrU
  have hxnrBound : ‖x + (n : ℝ) • r‖ ≤ C := hC _ hxnrQ
  have hnrBound : (n : ℝ) ≤ C + ‖x‖ := by
    calc
      (n : ℝ) = ‖(n : ℝ) • r‖ := by simp [norm_smul, hrNorm]
      _ ≤ ‖x + (n : ℝ) • r‖ + ‖x‖ := by
        have htriangle := norm_sub_le (x + (n : ℝ) • r) x
        simpa using htriangle
      _ ≤ C + ‖x‖ := by
        simpa [add_comm] using add_le_add_right hxnrBound ‖x‖
  exact (not_lt_of_ge hnrBound) hn

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
coordinatewise casting of integer vectors preserves addition. -/
lemma integerVectorCast_add
    {n : ℕ}
    (x y : Fin n → ℤ) :
    (Int.cast ∘ (x + y) : Fin n → ℝ) =
      (Int.cast ∘ x) + (Int.cast ∘ y) := by
  -- Integer casting commutes with addition in every coordinate.
  ext i
  simp

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
coordinatewise casting is an additive homomorphism from integer vectors to real vectors. -/
def integerVectorCastAddHom (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℝ) :=
  AddMonoidHom.mk' (fun z ↦ Int.cast ∘ z) integerVectorCast_add

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the linear image of the integer lattice is locally finite whenever it admits a bounded
full-dimensional maximal-free set. -/
lemma projectedIntegerVectors_locallyFinite_of_boundedMaximalFree
    {n q : ℕ}
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    {Q : Set (Fin q → ℝ)}
    (hQBounded : Bornology.IsBounded Q)
    (hQFull : affineSpan ℝ Q = ⊤)
    (hQMaximal : is_maximal_free_of (f '' (ℤ^n : Set (Fin n → ℝ))) Q) :
    ∀ B : Set (Fin q → ℝ), Bornology.IsBounded B →
      (B ∩ (f '' (ℤ^n : Set (Fin n → ℝ)))).Finite := by
  let castHom : (Fin n → ℤ) →+ (Fin n → ℝ) :=
    integerVectorCastAddHom n
  let S : AddSubgroup (Fin q → ℝ) :=
    AddMonoidHom.range (f.toAddMonoidHom.comp castHom)
  have hScarrier :
      (S : Set (Fin q → ℝ)) = f '' (ℤ^n : Set (Fin n → ℝ)) := by
    -- The range description removes all set-image arithmetic from the discreteness argument.
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Int.cast ∘ z, (mem_integerVectors_iff).2 ⟨z, rfl⟩, ?_⟩
      rfl
    · rintro ⟨x, hx, rfl⟩
      rcases (mem_integerVectors_iff.mp hx) with ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have hQInterior : (interior Q).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top
      (is_maximal_free_of.convex hQMaximal)).2 hQFull
  have hQMaximalS : is_maximal_free_of (S : Set (Fin q → ℝ)) Q := by
    rwa [hScarrier]
  have hSDiscrete : IsDiscrete (S : Set (Fin q → ℝ)) :=
    boundedMaximalFree_addSubgroup_isDiscrete S hQBounded hQInterior hQMaximalS
  intro B hB
  rw [← hScarrier]
  exact finite_inter_addSubgroup_of_isBounded_of_isDiscrete S hSDiscrete hB

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the coordinate box matrix records the upper and lower coordinate inequalities. -/
def coordinateBoxMatrix (q : ℕ) : Matrix (Fin (q + q)) (Fin q) ℝ :=
  fun i ↦ Fin.addCases (fun k ↦ Pi.single k 1) (fun k ↦ -Pi.single k 1) i

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
membership in the coordinate box polyhedron is coordinatewise membership in `[-R, R]`. -/
lemma mem_coordinateBoxPolyhedron_iff
    {q : ℕ}
    {R : ℝ}
    {x : Fin q → ℝ} :
    x ∈ polyhedron_le_set (coordinateBoxMatrix q) (fun _ ↦ R) ↔
      ∀ i : Fin q, -R ≤ x i ∧ x i ≤ R := by
  constructor
  · intro hx i
    have hupper := hx (Fin.castAdd q i)
    have hlower := hx (Fin.natAdd q i)
    have hupperRow : coordinateBoxMatrix q (Fin.castAdd q i) = Pi.single i 1 := by
      rw [coordinateBoxMatrix, Fin.addCases_left]
    have hlowerRow : coordinateBoxMatrix q (Fin.natAdd q i) = -Pi.single i 1 := by
      rw [coordinateBoxMatrix, Fin.addCases_right]
    constructor
    · rw [Matrix.mulVec, hlowerRow] at hlower
      rw [neg_dotProduct, single_dotProduct, one_mul] at hlower
      linarith
    · rw [Matrix.mulVec, hupperRow] at hupper
      simpa only [single_dotProduct, one_mul] using hupper
  · intro hx row
    refine Fin.addCases ?_ ?_ row
    · intro i
      have hrow : coordinateBoxMatrix q (Fin.castAdd q i) = Pi.single i 1 := by
        rw [coordinateBoxMatrix, Fin.addCases_left]
      rw [Matrix.mulVec, hrow]
      simpa only [single_dotProduct, one_mul] using (hx i).2
    · intro i
      have hrow : coordinateBoxMatrix q (Fin.natAdd q i) = -Pi.single i 1 := by
        rw [coordinateBoxMatrix, Fin.addCases_right]
      rw [Matrix.mulVec, hrow]
      rw [neg_dotProduct, single_dotProduct, one_mul]
      linarith [(hx i).1]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a coordinate box with nonnegative radius is bounded. -/
lemma coordinateBoxPolyhedron_isBounded
    {q : ℕ}
    {R : ℝ}
    (hR : 0 ≤ R) :
    Bornology.IsBounded
      (polyhedron_le_set (coordinateBoxMatrix q) (fun _ ↦ R)) := by
  -- Coordinatewise bounds control the supremum norm on the finite product.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R, ?_⟩
  intro x hx
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  exact abs_le.mpr ((mem_coordinateBoxPolyhedron_iff.mp hx) i)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the row formed from the coordinate values of a linear functional evaluates to that functional. -/
lemma dualCoordinateRow_mulVec
    {q : ℕ}
    (f : (Fin q → ℝ) →L[ℝ] ℝ)
    (x : Fin q → ℝ) :
    (fun j ↦ f (Pi.single j 1)) ⬝ᵥ x = f x := by
  -- Expand `x` in the standard coordinate basis and use linearity of `f`.
  symm
  calc
    f x = f (∑ i, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, f (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i, x i * f (Pi.single i 1) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [show Pi.single i (x i) = x i • Pi.single i (1 : ℝ) by
        ext j
        by_cases hij : j = i
        · subst hij
          simp
        · simp [Pi.single_eq_of_ne hij]]
      simp
    _ = (fun i ↦ f (Pi.single i 1)) ⬝ᵥ x := by
      simp [dotProduct, mul_comm]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a bounded full-dimensional maximal-free set for a locally finite forbidden set is a polyhedron. -/
lemma boundedMaximalLocallyFiniteFree_isPolyhedron
    {q : ℕ}
    {S Q : Set (Fin q → ℝ)}
    (hLocal : ∀ B : Set (Fin q → ℝ), Bornology.IsBounded B → (B ∩ S).Finite)
    (hQBounded : Bornology.IsBounded Q)
    (hQFull : affineSpan ℝ Q = ⊤)
    (hQMaximal : is_maximal_free_of S Q) :
    is_polyhedron Q := by
  classical
  have hQConvex : Convex ℝ Q := is_maximal_free_of.convex hQMaximal
  have hQInterior : (interior Q).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hQConvex).2 hQFull
  have hQClosed : IsClosed Q := by
    -- Maximality identifies `Q` with its closure because convex closure preserves the interior.
    have hClosureFree : is_free_of S (closure Q) := by
      rw [is_free_of_iff]
      intro s hsS hsClosure
      rw [hQConvex.interior_closure_eq_interior_of_nonempty_interior hQInterior] at hsClosure
      exact (is_free_of.not_mem_interior (is_maximal_free_of.free hQMaximal) hsS) hsClosure
    have hClosureEq : closure Q = Q :=
      is_maximal_free_of.eq_of_subset hQMaximal subset_closure hQConvex.closure hClosureFree
    exact closure_eq_iff_isClosed.mp hClosureEq
  have hClosureInterior : closure (interior Q) = Q := by
    calc
      closure (interior Q) = closure Q :=
        hQConvex.closure_interior_eq_closure_of_nonempty_interior hQInterior
      _ = Q := hQClosed.closure_eq
  obtain ⟨R, hRPos, hQBox⟩ := hQBounded.subset_ball_lt 0 0
  let C : Set (Fin q → ℝ) :=
    polyhedron_le_set (coordinateBoxMatrix q) (fun _ ↦ R)
  have hQSubsetC : Q ⊆ C := by
    -- The norm bound implies both coordinate inequalities of the enclosing box.
    intro x hxQ
    apply mem_coordinateBoxPolyhedron_iff.mpr
    intro i
    have hxi : |x i| < R :=
      (norm_le_pi_norm x i).trans_lt (by simpa [Metric.mem_ball, dist_zero_right] using hQBox hxQ)
    exact ⟨(abs_lt.mp hxi).1.le, (abs_lt.mp hxi).2.le⟩
  have hCBounded : Bornology.IsBounded C := by
    exact coordinateBoxPolyhedron_isBounded hRPos.le
  have hFinite : (C ∩ S).Finite := hLocal C hCBounded
  let T : Finset (Fin q → ℝ) := hFinite.toFinset
  have hTmem (s : Fin q → ℝ) : s ∈ T ↔ s ∈ C ∩ S := by
    exact hFinite.mem_toFinset
  have hOutsideInterior (s : ↑T) : (s : Fin q → ℝ) ∉ interior Q := by
    intro hsInterior
    exact
      (is_free_of.not_mem_interior (is_maximal_free_of.free hQMaximal)
        ((hTmem s).mp s.property).2) hsInterior
  have hSeparates (s : ↑T) :
      ∃ f : (Fin q → ℝ) →L[ℝ] ℝ,
        ∀ x ∈ interior Q, f x < f s :=
    geometric_hahn_banach_open_point hQConvex.interior isOpen_interior
      (hOutsideInterior s)
  choose f hf using hSeparates
  let e : Fin T.card ≃ ↑T := (Finset.equivFin T).symm
  let A : Matrix (Fin ((q + q) + T.card)) (Fin q) ℝ :=
    fun i ↦ Fin.addCases (coordinateBoxMatrix q)
      (fun k j ↦ f (e k) (Pi.single j 1)) i
  let b : Fin ((q + q) + T.card) → ℝ :=
    Fin.addCases (fun _ ↦ R) (fun k ↦ f (e k) (e k))
  let P : Set (Fin q → ℝ) := polyhedron_le_set A b
  have hQSubsetP : Q ⊆ P := by
    -- Closure of the interior transfers every strict separator to a valid weak inequality on `Q`.
    intro x hxQ row
    refine Fin.addCases ?_ ?_ row
    · intro i
      have hArow : A (Fin.castAdd T.card i) = coordinateBoxMatrix q i := by
        simp [A]
      have hbrow : b (Fin.castAdd T.card i) = R := by
        simp [b]
      rw [Matrix.mulVec, hArow, hbrow]
      exact hQSubsetC hxQ i
    · intro k
      have hHalfspaceClosed :
          IsClosed {y : Fin q → ℝ | f (e k) y ≤ f (e k) (e k)} :=
        isClosed_le (f (e k)).continuous continuous_const
      have hInteriorSubset :
          interior Q ⊆ {y : Fin q → ℝ | f (e k) y ≤ f (e k) (e k)} := by
        intro y hy
        exact (hf (e k) y hy).le
      have hxHalfspace := closure_minimal hInteriorSubset hHalfspaceClosed
        (show x ∈ closure (interior Q) by rwa [hClosureInterior])
      have hArow : A (Fin.natAdd (q + q) k) =
          fun j ↦ f (e k) (Pi.single j 1) := by
        simp [A]
      have hbrow : b (Fin.natAdd (q + q) k) = f (e k) (e k) := by
        simp [b]
      rw [Matrix.mulVec, hArow, hbrow, dualCoordinateRow_mulVec]
      exact hxHalfspace
  have hPSubsetC : P ⊆ C := by
    -- The first block of rows of `P` is precisely the coordinate box.
    intro x hx row
    have hArow : A (Fin.castAdd T.card row) = coordinateBoxMatrix q row := by
      simp [A]
    have hbrow : b (Fin.castAdd T.card row) = R := by
      simp [b]
    have hrow := hx (Fin.castAdd T.card row)
    rwa [Matrix.mulVec, hArow, hbrow] at hrow
  have hPFree : is_free_of S P := by
    rw [is_free_of_iff]
    intro s hsS hsInterior
    have hsP : s ∈ P := interior_subset hsInterior
    have hsC : s ∈ C := hPSubsetC hsP
    let st : ↑T := ⟨s, (hTmem s).mpr ⟨hsC, hsS⟩⟩
    let k : Fin T.card := e.symm st
    have hk : e k = st := e.apply_symm_apply st
    have hfNe : f st ≠ 0 := by
      intro hfZero
      rcases hQInterior with ⟨x, hx⟩
      have hstrict := hf st x hx
      rw [hfZero] at hstrict
      simp at hstrict
    have hPSubsetHalfspace :
        P ⊆ (f st) ⁻¹' Set.Iic (f st st) := by
      intro y hy
      have hrow := hy (Fin.natAdd (q + q) k)
      have hArow : A (Fin.natAdd (q + q) k) =
          fun j ↦ f (e k) (Pi.single j 1) := by
        simp [A]
      have hbrow : b (Fin.natAdd (q + q) k) = f (e k) (e k) := by
        simp [b]
      rw [Matrix.mulVec, hArow, hbrow, dualCoordinateRow_mulVec, hk] at hrow
      exact hrow
    have hsHalfspaceInterior :
        s ∈ interior ((f st) ⁻¹' Set.Iic (f st st)) :=
      interior_mono hPSubsetHalfspace hsInterior
    have hsStrict : f st s < f st st := by
      have hOpen : IsOpenMap (f st) := (f st).isOpenMap_of_ne_zero hfNe
      have hsPreimage : s ∈ (f st) ⁻¹' interior (Set.Iic (f st st)) := by
        rw [hOpen.preimage_interior_eq_interior_preimage (f st).continuous]
        exact hsHalfspaceInterior
      simpa using hsPreimage
    have hstEq : (st : Fin q → ℝ) = s := rfl
    rw [hstEq] at hsStrict
    exact (lt_irrefl _ hsStrict)
  have hPConvex : Convex ℝ P := by
    -- Each row inequality is preserved by convex combinations.
    intro x hx y hy a₁ a₂ ha₁ ha₂ haSum row
    have hrow := add_le_add
      (mul_le_mul_of_nonneg_left (hx row) ha₁)
      (mul_le_mul_of_nonneg_left (hy row) ha₂)
    calc
      Matrix.mulVec A (a₁ • x + a₂ • y) row =
          a₁ * Matrix.mulVec A x row + a₂ * Matrix.mulVec A y row := by
            simp [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ ≤ a₁ * b row + a₂ * b row := hrow
      _ = b row := by rw [← add_mul, haSum, one_mul]
  have hPEq : P = Q :=
    is_maximal_free_of.eq_of_subset hQMaximal hQSubsetP hPConvex hPFree
  -- The explicit finite separator system is therefore a presentation of `Q`.
  exact (is_polyhedron_iff.mpr ⟨(q + q) + T.card, A, b, hPEq.symm⟩)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the polyhedron obtained by omitting one row from a finite inequality system. -/
def polyhedronWithoutRow
    {m q : ℕ}
    (A : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m) : Set (Fin q → ℝ) :=
  {x | ∀ i : Fin m, i ≠ j → Matrix.mulVec A x i ≤ b i}

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
strict satisfaction of every nonimplicit row other than `j` puts a point in the interior of
`polyhedronWithoutRow A b j` when the original polyhedron is full-dimensional. -/
lemma memInterior_polyhedronWithoutRow_of_strict_nonimplicit
    {m q : ℕ}
    {A : Matrix (Fin m) (Fin q) ℝ}
    {b : Fin m → ℝ}
    {j : Fin m}
    {x : Fin q → ℝ}
    (hfull : affineSpan ℝ (polyhedron_le_set A b) = ⊤)
    (hstrict : ∀ i : Fin m, i ≠ j → ¬ is_implicit_equality A b i →
      Matrix.mulVec A x i < b i) :
    x ∈ interior (polyhedronWithoutRow A b j) := by
  classical
  let U : Set (Fin q → ℝ) :=
    {y | ∀ i : Fin m, i ≠ j → ¬ is_implicit_equality A b i →
      Matrix.mulVec A y i < b i}
  have hUOpen : IsOpen U := by
    let V : Fin m → Set (Fin q → ℝ) := fun i ↦
      if i ≠ j ∧ ¬ is_implicit_equality A b i then
        {y : Fin q → ℝ | Matrix.mulVec A y i < b i}
      else Set.univ
    have hUeq :
        U = ⋂ i : Fin m, V i := by
      ext y
      constructor
      · intro hy
        rw [Set.mem_iInter]
        intro i
        dsimp [V]
        split
        · rename_i hi
          exact hy i hi.1 hi.2
        · exact Set.mem_univ y
      · intro hy i hij hiImplicit
        have hyi := Set.mem_iInter.mp hy i
        dsimp [V] at hyi
        rw [if_pos ⟨hij, hiImplicit⟩] at hyi
        exact hyi
    rw [hUeq]
    refine isOpen_iInter_of_finite fun i ↦ ?_
    dsimp [V]
    split_ifs
    · exact isOpen_lt (by continuity) continuous_const
    · exact isOpen_univ
  have hImplicitGlobal (i : Fin m) (hi : is_implicit_equality A b i)
      (y : Fin q → ℝ) : Matrix.mulVec A y i = b i := by
    have hPolySubset :
        polyhedron_le_set A b ⊆ {z : Fin q → ℝ | A i ⬝ᵥ z = b i} := by
      intro z hz
      simpa [Matrix.mulVec] using hi hz
    have hSpanSubset :=
      affineSpan_subset_hyperplane_of_subset (c := A i) (δ := b i) hPolySubset
    have hySpan : y ∈ affineSpan ℝ (polyhedron_le_set A b) := by
      rw [hfull]
      exact (show y ∈ (⊤ : AffineSubspace ℝ (Fin q → ℝ)) by simp)
    simpa [Matrix.mulVec] using hSpanSubset hySpan
  have hUSubset : U ⊆ polyhedronWithoutRow A b j := by
    intro y hy i hij
    by_cases hi : is_implicit_equality A b i
    · exact (hImplicitGlobal i hi y).le
    · exact (hy i hij hi).le
  -- The strict-row neighborhood is open and lies in the row-deleted polyhedron.
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hUOpen.mem_nhds hstrict) hUSubset

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
an interior point of the row-deleted system that satisfies the omitted row strictly is an
interior point of the full polyhedron. -/
lemma memInterior_polyhedron_of_memInterior_withoutRow_of_row_lt
    {m q : ℕ}
    {A : Matrix (Fin m) (Fin q) ℝ}
    {b : Fin m → ℝ}
    {j : Fin m}
    {x : Fin q → ℝ}
    (hother : x ∈ interior (polyhedronWithoutRow A b j))
    (hrow : Matrix.mulVec A x j < b j) :
    x ∈ interior (polyhedron_le_set A b) := by
  let U : Set (Fin q → ℝ) :=
    interior (polyhedronWithoutRow A b j) ∩
      {y : Fin q → ℝ | Matrix.mulVec A y j < b j}
  have hUOpen : IsOpen U :=
    isOpen_interior.inter (isOpen_lt (by continuity) continuous_const)
  have hUSubset : U ⊆ polyhedron_le_set A b := by
    intro y hy i
    by_cases hij : i = j
    · subst hij
      exact hy.2.le
    · exact (interior_subset hy.1) i hij
  -- Intersect the two open neighborhoods witnessing the other rows and the omitted row.
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hUOpen.mem_nhds ⟨hother, hrow⟩) hUSubset

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a point interior to the row-deleted system and tight on the omitted row lies in the intrinsic
interior of the corresponding singleton active face. -/
lemma memIntrinsicInterior_singletonActiveFace_of_memInterior_withoutRow
    {m q : ℕ}
    {A : Matrix (Fin m) (Fin q) ℝ}
    {b : Fin m → ℝ}
    {j : Fin m}
    {x : Fin q → ℝ}
    (hother : x ∈ interior (polyhedronWithoutRow A b j))
    (hrow : Matrix.mulVec A x j = b j) :
    x ∈ intrinsicInterior ℝ
      (active_constraint_face A b ({j} : Set (Fin m))) := by
  let F : Set (Fin q → ℝ) := active_constraint_face A b ({j} : Set (Fin m))
  have hxFace : x ∈ F := by
    refine (mem_active_constraint_face_iff).2 ⟨?_, ?_⟩
    · intro i hi
      have hij : i = j := by simpa using hi
      simpa [hij] using hrow
    · intro i _hi
      by_cases hij : i = j
      · simpa [hij] using hrow.le
      · exact (interior_subset hother) i hij
  have hFaceHyperplane : F ⊆ {y : Fin q → ℝ | A j ⬝ᵥ y = b j} := by
    intro y hy
    have hyRow := (mem_active_constraint_face_iff.mp hy).1 j (by simp)
    simpa [Matrix.mulVec] using hyRow
  have hSpanHyperplane :=
    affineSpan_subset_hyperplane_of_subset (c := A j) (δ := b j) hFaceHyperplane
  let xAff : affineSpan ℝ F := ⟨x, subset_affineSpan ℝ F hxFace⟩
  refine mem_intrinsicInterior.mpr ⟨xAff, ?_, rfl⟩
  let U : Set (affineSpan ℝ F) :=
    ((↑) : affineSpan ℝ F → Fin q → ℝ) ⁻¹'
      interior (polyhedronWithoutRow A b j)
  have hUOpen : IsOpen U := isOpen_interior.preimage continuous_subtype_val
  have hxAffU : xAff ∈ U := hother
  have hUSubset : U ⊆ ((↑) ⁻¹' F : Set (affineSpan ℝ F)) := by
    intro y hy
    have hyRow : A j ⬝ᵥ (y : Fin q → ℝ) = b j := hSpanHyperplane y.property
    refine (mem_active_constraint_face_iff).2 ⟨?_, ?_⟩
    · intro i hi
      have hij : i = j := by simpa using hi
      simpa [Matrix.mulVec, hij] using hyRow
    · intro i _hi
      by_cases hij : i = j
      · simpa [Matrix.mulVec, hij] using hyRow.le
      · exact (interior_subset hy) i hij
  -- Relative openness is witnessed by the ambiently open row-deleted neighborhood.
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hUOpen.mem_nhds hxAffU) hUSubset

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a finite family of positive real numbers has a common positive strict lower bound. -/
lemma exists_commonPositiveLowerBound_finset
    {α : Type*}
    (T : Finset α)
    (g : α → ℝ)
    (hg : ∀ x ∈ T, 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ T, δ < g x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨1, zero_lt_one, by simp⟩
  | insert a T ha ih =>
      have hga : 0 < g a := hg a (by simp)
      have hgT : ∀ x ∈ T, 0 < g x := by
        intro x hx
        exact hg x (by simp [hx])
      rcases ih hgT with ⟨δ, hδ, hδT⟩
      refine ⟨min δ (g a) / 2, by positivity, ?_⟩
      intro x hx
      by_cases hxa : x = a
      · subst x
        have hmin : min δ (g a) ≤ g a := min_le_right _ _
        linarith
      · have hxT : x ∈ T := by simpa [hxa] using hx
        have hmin : min δ (g a) ≤ δ := min_le_left _ _
        linarith [hδT x hxT]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a finite system of linear weak inequalities defines a convex set. -/
lemma matrixPolyhedron_convex
    {m q : ℕ}
    (A : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  intro x hx y hy a₁ a₂ ha₁ ha₂ haSum i
  have hle := add_le_add
    (mul_le_mul_of_nonneg_left (hx i) ha₁)
    (mul_le_mul_of_nonneg_left (hy i) ha₂)
  calc
    Matrix.mulVec A (a₁ • x + a₂ • y) i =
        a₁ * Matrix.mulVec A x i + a₂ * Matrix.mulVec A y i := by
          simp [Matrix.mulVec_add, Matrix.mulVec_smul]
    _ ≤ a₁ * b i + a₂ * b i := hle
    _ = b i := by rw [← add_mul, haSum, one_mul]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a nonzero valid inequality is strict at every interior point of its feasible set. -/
lemma strict_of_memInterior_of_validInequality
    {q : ℕ}
    {P : Set (Fin q → ℝ)}
    {c x : Fin q → ℝ}
    {β : ℝ}
    (hc : c ≠ 0)
    (hvalid : is_valid_inequality P c β)
    (hx : x ∈ interior P) :
    c ⬝ᵥ x < β := by
  have hxLe : c ⬝ᵥ x ≤ β := hvalid (interior_subset hx)
  apply lt_of_le_of_ne hxLe
  intro hxEq
  rw [mem_interior_iff_mem_nhds] at hx
  rcases Metric.mem_nhds_iff.mp hx with ⟨ε, hεPos, hεSubset⟩
  have hcNormPos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hselfNonneg : 0 ≤ c ⬝ᵥ c := by
    unfold dotProduct
    exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (c i))
  have hselfNe : c ⬝ᵥ c ≠ 0 := by
    intro hzero
    exact hc (dotProduct_self_eq_zero.mp hzero)
  have hselfPos : 0 < c ⬝ᵥ c := lt_of_le_of_ne hselfNonneg (Ne.symm hselfNe)
  let a : ℝ := ε / (2 * ‖c‖)
  have haPos : 0 < a := by
    dsimp [a]
    positivity
  have haNorm : ‖a • c‖ < ε := by
    calc
      ‖a • c‖ = |a| * ‖c‖ := norm_smul _ _
      _ = a * ‖c‖ := by rw [abs_of_pos haPos]
      _ = ε / 2 := by
        dsimp [a]
        field_simp [hcNormPos.ne']
      _ < ε := by linarith
  have hperturbedBall : x + a • c ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using haNorm
  have hperturbedLe : c ⬝ᵥ (x + a • c) ≤ β :=
    hvalid (hεSubset hperturbedBall)
  have hperturbedGt : β < c ⬝ᵥ (x + a • c) := by
    rw [dotProduct_add, dotProduct_smul, hxEq, smul_eq_mul]
    nlinarith
  exact (not_lt_of_ge hperturbedLe) hperturbedGt

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
each irredundant facet row of a bounded full-dimensional maximal-free polyhedron contains a
forbidden point that is tight on that row and interior to the system with that row omitted. -/
lemma boundedMaximalLocallyFiniteFree_singletonFacetContact
    {m q : ℕ}
    {S : Set (Fin q → ℝ)}
    {A : Matrix (Fin m) (Fin q) ℝ}
    {b : Fin m → ℝ}
    (hLocal : ∀ B : Set (Fin q → ℝ), Bornology.IsBounded B → (B ∩ S).Finite)
    (hBounded : Bornology.IsBounded (polyhedron_le_set A b))
    (hFull : affineSpan ℝ (polyhedron_le_set A b) = ⊤)
    (hMaximal : is_maximal_free_of S (polyhedron_le_set A b))
    (j : Fin m)
    (hjRemaining : j ∈ remaining_inequality_indices A b)
    (hjIrredundant : is_irredundant_row A b j) :
    ∃ s : Fin q → ℝ, s ∈ S ∧
      s ∈ interior (polyhedronWithoutRow A b j) ∧
        Matrix.mulVec A s j = b j := by
  classical
  by_contra hNoContact
  push Not at hNoContact
  have hConvex : Convex ℝ (polyhedron_le_set A b) := matrixPolyhedron_convex A b
  have hInterior : (interior (polyhedron_le_set A b)).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hConvex).2 hFull
  have hNonempty : (polyhedron_le_set A b).Nonempty := hInterior.mono interior_subset
  obtain ⟨xhat, hxhatFace, hxhatStrict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A b j hNonempty hjIrredundant
  have hxhatPoly : xhat ∈ polyhedron_le_set A b :=
    mem_polyhedron_of_mem_active_constraint_face hxhatFace
  have hxhatRow : Matrix.mulVec A xhat j = b j :=
    (mem_active_constraint_face_iff.mp hxhatFace).1 j (by simp)
  have hxhatOther : xhat ∈ interior (polyhedronWithoutRow A b j) :=
    memInterior_polyhedronWithoutRow_of_strict_nonimplicit hFull hxhatStrict
  have hjNotImplicit : ¬ is_implicit_equality A b j :=
    (mem_remaining_inequality_indices_iff A b j).1 hjRemaining
  have hrowNe : A j ≠ 0 := by
    intro hrowZero
    apply hjNotImplicit
    intro x hx
    have hbZero : b j = 0 := by
      simpa [Matrix.mulVec, hrowZero] using hxhatRow.symm
    simp [Matrix.mulVec, hrowZero, hbZero]
  obtain ⟨R, hRPos, hPolyBall⟩ := hBounded.subset_ball_lt 0 0
  let C : Set (Fin q → ℝ) :=
    polyhedron_le_set (coordinateBoxMatrix q) (fun _ ↦ R)
  have hBallSubsetC : Metric.ball (0 : Fin q → ℝ) R ⊆ C := by
    intro x hx
    apply mem_coordinateBoxPolyhedron_iff.mpr
    intro i
    have hxi : |x i| < R :=
      (norm_le_pi_norm x i).trans_lt (by
        simpa [Metric.mem_ball, dist_zero_right] using hx)
    exact ⟨(abs_lt.mp hxi).1.le, (abs_lt.mp hxi).2.le⟩
  have hPolySubsetInteriorC : polyhedron_le_set A b ⊆ interior C := by
    intro x hx
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (hPolyBall hx)) hBallSubsetC
  have hCBounded : Bornology.IsBounded C :=
    coordinateBoxPolyhedron_isBounded hRPos.le
  have hFinite : (C ∩ S).Finite := hLocal C hCBounded
  let T : Finset (Fin q → ℝ) := hFinite.toFinset
  have hTmem (s : Fin q → ℝ) : s ∈ T ↔ s ∈ C ∩ S := hFinite.mem_toFinset
  let G : Finset (Fin q → ℝ) :=
    T.filter fun s ↦ s ∈ interior (polyhedronWithoutRow A b j)
  have hGapPos (s : Fin q → ℝ) (hsG : s ∈ G) :
      0 < Matrix.mulVec A s j - b j := by
    have hsT : s ∈ T := (Finset.mem_filter.mp hsG).1
    have hsS : s ∈ S := ((hTmem s).mp hsT).2
    have hsOther : s ∈ interior (polyhedronWithoutRow A b j) :=
      (Finset.mem_filter.mp hsG).2
    have hsNotInterior : s ∉ interior (polyhedron_le_set A b) :=
      is_free_of.not_mem_interior (is_maximal_free_of.free hMaximal) hsS
    have hnotLt : ¬ Matrix.mulVec A s j < b j := by
      intro hsLt
      exact hsNotInterior
        (memInterior_polyhedron_of_memInterior_withoutRow_of_row_lt hsOther hsLt)
    have hnotEq : Matrix.mulVec A s j ≠ b j := by
      intro hsEq
      exact hNoContact s hsS hsOther hsEq
    exact sub_pos.mpr (lt_of_le_of_ne (not_lt.mp hnotLt) (Ne.symm hnotEq))
  obtain ⟨δ, hδPos, hδGap⟩ :=
    exists_commonPositiveLowerBound_finset G
      (fun s ↦ Matrix.mulVec A s j - b j) hGapPos
  let bRelaxed : Fin m → ℝ := Function.update b j (b j + δ)
  let PRelaxed : Set (Fin q → ℝ) := C ∩ polyhedron_le_set A bRelaxed
  have hPolySubsetRelaxed : polyhedron_le_set A b ⊆ PRelaxed := by
    intro x hx
    refine ⟨interior_subset (hPolySubsetInteriorC hx), ?_⟩
    intro i
    by_cases hij : i = j
    · rw [hij]
      simp [bRelaxed]
      exact (hx j).trans (le_add_of_nonneg_right hδPos.le)
    · simpa [bRelaxed, hij] using hx i
  have hRelaxedConvex : Convex ℝ PRelaxed := by
    exact (matrixPolyhedron_convex _ _).inter (matrixPolyhedron_convex _ _)
  rcases hjIrredundant with ⟨y, hyOther, hyRow⟩
  let d : Fin q → ℝ := y - xhat
  let gap : ℝ := Matrix.mulVec A y j - b j
  let margin : ℝ := R - ‖xhat‖
  have hgapPos : 0 < gap := sub_pos.mpr hyRow
  have hdNe : d ≠ 0 := by
    intro hdZero
    have hyEq : y = xhat := sub_eq_zero.mp hdZero
    rw [hyEq, hxhatRow] at hyRow
    exact (lt_irrefl _ hyRow)
  have hdNormPos : 0 < ‖d‖ := norm_pos_iff.mpr hdNe
  have hmarginPos : 0 < margin := by
    have hxhatBall := hPolyBall hxhatPoly
    simpa [margin, Metric.mem_ball, dist_zero_right] using hxhatBall
  let bound : ℝ := min 1 (min (δ / gap) (margin / ‖d‖))
  let t : ℝ := bound / 2
  have hboundPos : 0 < bound := by
    dsimp [bound]
    exact lt_min zero_lt_one (lt_min (div_pos hδPos hgapPos) (div_pos hmarginPos hdNormPos))
  have htPos : 0 < t := by
    dsimp [t]
    positivity
  have htLtBound : t < bound := by
    dsimp [t]
    linarith
  have htLtOne : t < 1 := htLtBound.trans_le (min_le_left _ _)
  have htGap : t * gap < δ := by
    have ht : t < δ / gap :=
      htLtBound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    exact (lt_div_iff₀ hgapPos).mp ht
  have htNorm : t * ‖d‖ < margin := by
    have ht : t < margin / ‖d‖ :=
      htLtBound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    exact (lt_div_iff₀ hdNormPos).mp ht
  let yout : Fin q → ℝ := xhat + t • d
  have hyoutBall : yout ∈ Metric.ball (0 : Fin q → ℝ) R := by
    have hnorm : ‖yout‖ ≤ ‖xhat‖ + t * ‖d‖ := by
      calc
        ‖yout‖ ≤ ‖xhat‖ + ‖t • d‖ := norm_add_le _ _
        _ = ‖xhat‖ + t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos htPos]
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [margin] at htNorm
    linarith
  have hyoutRelaxedRows : yout ∈ polyhedron_le_set A bRelaxed := by
    intro i
    by_cases hij : i = j
    · rw [hij]
      have hrowFormula : Matrix.mulVec A yout j = b j + t * gap := by
        dsimp [yout, d, gap]
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
          Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [hxhatRow]
      rw [hrowFormula]
      simpa [bRelaxed] using htGap.le
    · have hxhatLe := hxhatPoly i
      have hyLe := hyOther i hij
      have hrowFormula :
          Matrix.mulVec A yout i =
            (1 - t) * Matrix.mulVec A xhat i + t * Matrix.mulVec A y i := by
        dsimp [yout, d]
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
          Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [hrowFormula]
      have htNonneg : 0 ≤ t := htPos.le
      have honeNonneg : 0 ≤ 1 - t := sub_nonneg.mpr htLtOne.le
      have hle := add_le_add
        (mul_le_mul_of_nonneg_left hxhatLe honeNonneg)
        (mul_le_mul_of_nonneg_left hyLe htNonneg)
      simpa [bRelaxed, hij, ← add_mul] using hle
  have hyoutRelaxed : yout ∈ PRelaxed :=
    ⟨hBallSubsetC hyoutBall, hyoutRelaxedRows⟩
  have hyoutNotPoly : yout ∉ polyhedron_le_set A b := by
    intro hyoutPoly
    have hrowFormula : Matrix.mulVec A yout j = b j + t * gap := by
      dsimp [yout, d, gap]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
        Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hxhatRow]
    have hyoutLe := hyoutPoly j
    rw [hrowFormula] at hyoutLe
    nlinarith
  have hRelaxedNotFree : ¬ is_free_of S PRelaxed := by
    intro hFree
    have hEq : PRelaxed = polyhedron_le_set A b :=
      is_maximal_free_of.eq_of_subset hMaximal hPolySubsetRelaxed hRelaxedConvex hFree
    exact hyoutNotPoly (by rwa [← hEq])
  rw [is_free_of_iff] at hRelaxedNotFree
  push Not at hRelaxedNotFree
  rcases hRelaxedNotFree with ⟨s, hsS, hsInterior⟩
  have hsRelaxed : s ∈ PRelaxed := interior_subset hsInterior
  have hsT : s ∈ T := (hTmem s).mpr ⟨hsRelaxed.1, hsS⟩
  have hRelaxedSubsetOther : PRelaxed ⊆ polyhedronWithoutRow A b j := by
    intro x hx i hij
    have hxi := hx.2 i
    simpa [bRelaxed, hij] using hxi
  have hsOther : s ∈ interior (polyhedronWithoutRow A b j) :=
    interior_mono hRelaxedSubsetOther hsInterior
  have hsG : s ∈ G := Finset.mem_filter.mpr ⟨hsT, hsOther⟩
  have hsmallGap : δ < Matrix.mulVec A s j - b j := hδGap s hsG
  have hRelaxedValid : is_valid_inequality PRelaxed (A j) (b j + δ) := by
    intro x hx
    have hxj := hx.2 j
    simpa [Matrix.mulVec, bRelaxed] using hxj
  have hsRowLt : Matrix.mulVec A s j < b j + δ := by
    simpa [Matrix.mulVec] using
      strict_of_memInterior_of_validInequality hrowNe hRelaxedValid hsInterior
  linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
matrix multiplication by `LinearMap.toMatrix' f` computes row functionals after applying `f`. -/
lemma matrixMulVec_comp_linearMap
    {m n q : ℕ}
    (A : Matrix (Fin m) (Fin q) ℝ)
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (x : Fin n → ℝ) :
    Matrix.mulVec (A * LinearMap.toMatrix' f) x = Matrix.mulVec A (f x) := by
  -- Normalize the composite matrix action before any rowwise reasoning.
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
pulling back a finite inequality system along a linear map composes its matrix with that map. -/
lemma polyhedron_preimage_linearMap_eq
    {m n q : ℕ}
    (A : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ)
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)) :
    f ⁻¹' polyhedron_le_set A b =
      polyhedron_le_set (A * LinearMap.toMatrix' f) b := by
  -- The two systems have identical row values after the matrix-composition normalization.
  ext x
  simp only [Set.mem_preimage, mem_polyhedron_le_set_iff]
  rw [matrixMulVec_comp_linearMap]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
deleting a row commutes with pulling a finite inequality system back along a linear map. -/
lemma polyhedronWithoutRow_preimage_linearMap_eq
    {m n q : ℕ}
    (A : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)) :
    f ⁻¹' polyhedronWithoutRow A b j =
      polyhedronWithoutRow (A * LinearMap.toMatrix' f) b j := by
  -- Omitting a row does not affect the same rowwise matrix-composition identity.
  ext x
  simp only [Set.mem_preimage, polyhedronWithoutRow, Set.mem_setOf_eq]
  rw [matrixMulVec_comp_linearMap]

/-- Helper for Theorem 6.18: once `recessionCone K = linealitySpace K`, the remaining forward
direction reduces to a bounded quotient argument that yields both polyhedrality and facet lattice
witnesses. -/
lemma maximalLatticeFree_polyhedralFacets_of_recessionEqLineality
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K)
    (hrec : recessionCone K = linealitySpace K) :
    is_polyhedron K ∧
      ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
        ∃ z : Fin p → ℤ, (Int.cast ∘ z) ∈ intrinsicInterior ℝ F := by
  -- Route correction: the forward implication should now factor through theorem (2) and a bounded
  -- quotient reduction instead of replaying the bounded source proof directly in the theorem body.
  have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
  have hclosed : IsClosed K := maximalLatticeFree_isClosed hfull hK
  have hqBounded :
      Bornology.IsBounded ((linealityQuotientCoordinateMap K) '' K) :=
    linealityQuotientImage_bounded_of_recessionEqLineality hconv hclosed hrec
  have hqInterface := linealityQuotientImage_maximalProjectedIntegerFree hfull hK
  rcases hqInterface with ⟨hqFull, hqMaximalFree⟩
  let π := linealityQuotientCoordinateMap K
  have hqLocal :
      ∀ B : Set (Fin (Module.finrank ℝ ((Fin p → ℝ) ⧸ linealitySubmodule K)) → ℝ),
        Bornology.IsBounded B →
          (B ∩ (π '' (ℤ^p : Set (Fin p → ℝ)))).Finite :=
    projectedIntegerVectors_locallyFinite_of_boundedMaximalFree
      π hqBounded hqFull hqMaximalFree
  have hqPoly : is_polyhedron (π '' K) :=
    boundedMaximalLocallyFiniteFree_isPolyhedron hqLocal hqBounded hqFull hqMaximalFree
  refine ⟨isPolyhedron_of_linealityQuotientImage_isPolyhedron hqPoly, ?_⟩
  rcases is_polyhedron_iff.mp hqPoly with ⟨m, A, b, hqPresentation⟩
  rcases exists_equivalent_row_irredundant_representation A b with
    ⟨A', b', hsamePolyhedron, hminimal⟩
  have hqRepresentation : π '' K = polyhedron_le_set A' b' :=
    hqPresentation.trans hsamePolyhedron.symm
  let C : Matrix (Fin m) (Fin p) ℝ := A' * LinearMap.toMatrix' π
  have hKRepresentation : K = polyhedron_le_set C b' := by
    -- Pull the minimal quotient presentation back through the saturated quotient map.
    calc
      K = π ⁻¹' (π '' K) := (linealityQuotientImage_preimage_eq (K := K)).symm
      _ = π ⁻¹' polyhedron_le_set A' b' :=
        congrArg (fun Q : Set _ ↦ π ⁻¹' Q) hqRepresentation
      _ = polyhedron_le_set C b' := by
        simpa [C] using polyhedron_preimage_linearMap_eq A' b' π
  have hqPresentedBounded : Bornology.IsBounded (polyhedron_le_set A' b') := by
    rwa [← hqRepresentation]
  have hqPresentedFull : affineSpan ℝ (polyhedron_le_set A' b') = ⊤ := by
    rwa [← hqRepresentation]
  have hqPresentedMaximal :
      is_maximal_free_of (π '' (ℤ^p : Set (Fin p → ℝ)))
        (polyhedron_le_set A' b') := by
    rwa [← hqRepresentation]
  have hπSurjective : Function.Surjective π :=
    (linealityQuotientImage_interface hconv hclosed).1
  have hπOpen : IsOpenMap π :=
    LinearMap.isOpenMap_of_finiteDimensional π hπSurjective
  have hπContinuous : Continuous π := LinearMap.continuous_of_finiteDimensional π
  intro F hF
  have hFPresented : IsFacetOf (polyhedron_le_set C b') F := by
    rwa [← hKRepresentation]
  rcases isFacetOf_iff.mp hFPresented with
    ⟨hFNonempty, hFExposed, hFCodimension⟩
  have hPresentedNonempty : (polyhedron_le_set C b').Nonempty :=
    hFNonempty.mono hFExposed.subset
  have hFFacet : is_facet (polyhedron_le_set C b') F :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      C b' hPresentedNonempty F hFExposed).2 ⟨hFNonempty, hFCodimension⟩
  obtain ⟨j, hFRow⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet
      C b' hPresentedNonempty F hFFacet
  have hjPulledNotImplicit : ¬ is_implicit_equality C b' j.1 :=
    (mem_remaining_inequality_indices_iff C b' j.1).1 j.2
  have hjQuotientNotImplicit : ¬ is_implicit_equality A' b' j.1 := by
    intro hjImplicit
    apply hjPulledNotImplicit
    intro x hx
    have hxPreimage : x ∈ π ⁻¹' polyhedron_le_set A' b' := by
      rw [polyhedron_preimage_linearMap_eq A' b' π]
      simpa [C] using hx
    have hrowQuotient : Matrix.mulVec A' (π x) j.1 = b' j.1 :=
      hjImplicit hxPreimage
    have hrowComposite := congrFun (matrixMulVec_comp_linearMap A' π x) j.1
    exact hrowComposite.trans hrowQuotient
  have hjQuotientRemaining : j.1 ∈ remaining_inequality_indices A' b' :=
    (mem_remaining_inequality_indices_iff A' b' j.1).2 hjQuotientNotImplicit
  have hjQuotientIrredundant : is_irredundant_row A' b' j.1 :=
    hminimal j.1 hjQuotientNotImplicit
  obtain ⟨s, hsProjectedInteger, hsOtherRows, hsTightRow⟩ :=
    boundedMaximalLocallyFiniteFree_singletonFacetContact
      hqLocal hqPresentedBounded hqPresentedFull hqPresentedMaximal
        j.1 hjQuotientRemaining hjQuotientIrredundant
  rcases hsProjectedInteger with ⟨zReal, hzRealInteger, hzRealImage⟩
  rcases mem_integerVectors_iff.mp hzRealInteger with ⟨z, rfl⟩
  have hzPreimageInterior :
      (Int.cast ∘ z : Fin p → ℝ) ∈
        π ⁻¹' interior (polyhedronWithoutRow A' b' j.1) := by
    simpa [hzRealImage] using hsOtherRows
  have hzInteriorPreimage :
      (Int.cast ∘ z : Fin p → ℝ) ∈
        interior (π ⁻¹' polyhedronWithoutRow A' b' j.1) := by
    rw [← hπOpen.preimage_interior_eq_interior_preimage hπContinuous]
    exact hzPreimageInterior
  have hzOtherRows :
      (Int.cast ∘ z : Fin p → ℝ) ∈ interior (polyhedronWithoutRow C b' j.1) := by
    rw [← polyhedronWithoutRow_preimage_linearMap_eq A' b' j.1 π]
    exact hzInteriorPreimage
  have hzTightRow : Matrix.mulVec C (Int.cast ∘ z) j.1 = b' j.1 := by
    have hrowComposite :=
      congrFun (matrixMulVec_comp_linearMap A' π (Int.cast ∘ z)) j.1
    dsimp [C]
    rw [hrowComposite, hzRealImage]
    exact hsTightRow
  refine ⟨z, ?_⟩
  rw [hFRow]
  exact
    memIntrinsicInterior_singletonActiveFace_of_memInterior_withoutRow
      hzOtherRows hzTightRow

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
arbitrarily large natural multiples of a real vector approach an embedded integer vector. -/
lemma exists_large_nsmul_near_integerVector
    (r : Fin p → ℝ)
    {ε : ℝ}
    (hε : 0 < ε)
    (N : ℕ)
    (hN : 0 < N) :
    ∃ n : ℕ, N ≤ n ∧
      ∃ z : Fin p → ℤ, ‖(n : ℝ) • r - (Int.cast ∘ z)‖ < ε := by
  classical
  -- Apply compact-group recurrence to the class of `N • r` in the coordinate torus.
  let μ : MeasureTheory.Measure (Fin p → AddCircle (1 : ℝ)) :=
    MeasureTheory.Measure.pi fun _ : Fin p ↦ (volume : Measure (AddCircle (1 : ℝ)))
  let ξ : Fin p → AddCircle (1 : ℝ) :=
    fun i ↦ (((N : ℝ) * r i : ℝ) : AddCircle (1 : ℝ))
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hballPos :
      0 < μ (Metric.closedBall (0 : Fin p → AddCircle (1 : ℝ)) (δ / 2)) :=
    Metric.measure_closedBall_pos μ 0 (by positivity)
  have hunivFinite : μ (Set.univ : Set (Fin p → AddCircle (1 : ℝ))) ≠ ⊤ :=
    isCompact_univ.measure_lt_top.ne
  obtain ⟨m, hmPos, hm⟩ :=
    ENNReal.exists_nat_pos_mul_gt hballPos.ne' hunivFinite
  have hmeasure :
      μ Set.univ ≤
        (m + 1) • μ (Metric.closedBall (0 : Fin p → AddCircle (1 : ℝ)) (δ / 2)) := by
    have hm' :
        μ Set.univ <
          (m + 1 : ℕ) * μ (Metric.closedBall (0 : Fin p → AddCircle (1 : ℝ)) (δ / 2)) := by
      exact hm.trans_le (by
        gcongr
        omega)
    simpa [nsmul_eq_mul] using hm'.le
  obtain ⟨j, hj, hjNorm⟩ :=
    NormedAddCommGroup.exists_norm_nsmul_le (μ := μ) ξ hmPos δ hmeasure
  let n : ℕ := j * N
  let z : Fin p → ℤ := fun i ↦ round ((n : ℝ) * r i)
  refine ⟨n, ?_, z, ?_⟩
  · -- The recurrence multiplier is positive, so the resulting multiple is at least `N`.
    dsimp [n]
    exact Nat.le_mul_of_pos_left N hj.1
  · -- The torus norm is the maximum coordinate distance to the nearest integer.
    rw [← dist_zero_right]
    rw [dist_pi_lt_iff hε]
    intro i
    have hcoord : ‖(j • ξ) i‖ ≤ δ :=
      (norm_le_pi_norm (j • ξ) i).trans hjNorm
    change
      ‖j • ((((N : ℝ) * r i : ℝ)) : AddCircle (1 : ℝ))‖ ≤ δ at hcoord
    rw [← AddCircle.coe_nsmul, AddCircle.norm_eq] at hcoord
    have hcoord' : |(n : ℝ) * r i - (z i : ℝ)| ≤ δ := by
      simpa [n, z, nsmul_eq_mul, mul_assoc, mul_left_comm,
        mul_comm] using hcoord
    simpa [Real.dist_eq, Pi.smul_apply, Function.comp_apply] using hcoord'.trans_lt (by
      dsimp [δ]
      linarith)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
an interior point of a quotient image has a representative in the original interior. -/
lemma exists_interior_preimage_of_mem_interior_linearImage
    {qdim : ℕ}
    {K : Set (Fin p → ℝ)}
    (hconv : Convex ℝ K)
    (hKInterior : (interior K).Nonempty)
    (f : (Fin p → ℝ) →ₗ[ℝ] (Fin qdim → ℝ))
    {q : Fin qdim → ℝ}
    (hq : q ∈ interior (f '' K)) :
    ∃ x ∈ interior K, f x = q := by
  -- Move from a fixed interior lift toward a lift lying just beyond `q` in the quotient image.
  rcases hKInterior with ⟨x₀, hx₀⟩
  by_cases hx₀q : f x₀ = q
  · exact ⟨x₀, hx₀, hx₀q⟩
  rw [mem_interior_iff_mem_nhds] at hq
  rcases Metric.mem_nhds_iff.mp hq with ⟨ε, hε, hball⟩
  let v : Fin qdim → ℝ := q - f x₀
  have hv : v ≠ 0 := by
    intro hv0
    apply hx₀q
    dsimp [v] at hv0
    exact sub_eq_zero.mp hv0 |>.symm
  let t : ℝ := ε / (2 * ‖v‖)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hqtBall : q + t • v ∈ Metric.ball q ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    dsimp [t]
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    field_simp
    linarith
  rcases hball hqtBall with ⟨y, hyK, hyq⟩
  let s : ℝ := (1 + t)⁻¹
  have hsPos : 0 < s := by
    dsimp [s]
    positivity
  have hsLt : s < 1 := by
    dsimp [s]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  let x : Fin p → ℝ := (1 - s) • x₀ + s • y
  have hxInterior : x ∈ interior K := by
    dsimp [x]
    exact hconv.combo_interior_self_mem_interior hx₀ hyK (sub_pos.mpr hsLt) hsPos.le
      (sub_add_cancel 1 s)
  refine ⟨x, hxInterior, ?_⟩
  have hyq' : f y = q + t • (q - f x₀) := by
    simpa [v] using hyq
  dsimp [x]
  rw [map_add, map_smul, map_smul, hyq']
  have htOne : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hsOne : s * (1 + t) = 1 := by
    dsimp only [s]
    exact inv_mul_cancel₀ htOne
  calc
    (1 - s) • f x₀ + s • (q + t • (q - f x₀)) =
        (1 - s * (1 + t)) • f x₀ + (s * (1 + t)) • q := by module
    _ = q := by rw [hsOne]; simp

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a nonlineal recession direction of a full-dimensional closed convex lattice-free set permits a
strict convex lattice-free enlargement. -/
lemma existsStrictLatticeFreeEnlargement_of_recession_not_lineality
    {K : Set (Fin p → ℝ)}
    {r : Fin p → ℝ}
    (hfull : affineSpan ℝ K = ⊤)
    (hKfree : is_lattice_free K)
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    (hr : r ∈ recessionCone K)
    (hnot : r ∉ linealitySpace K) :
    ∃ L : Set (Fin p → ℝ), K ⊂ L ∧ Convex ℝ L ∧ is_lattice_free L := by
  classical
  -- Route correction: complete `K` along the whole line spanned by `r`; quotient openness and
  -- simultaneous recurrence show that this global completion is still lattice-free.
  let S : Submodule ℝ (Fin p → ℝ) := ℝ ∙ r
  let π : (Fin p → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ ((Fin p → ℝ) ⧸ S)) → ℝ) :=
    ((Module.finBasis ℝ ((Fin p → ℝ) ⧸ S)).equivFun.toLinearMap).comp S.mkQ
  let L : Set (Fin p → ℝ) := π ⁻¹' (π '' K)
  have hπSurj : Function.Surjective π := by
    exact
      (Module.finBasis ℝ ((Fin p → ℝ) ⧸ S)).equivFun.surjective.comp
        S.mkQ_surjective
  have hπKer : LinearMap.ker π = S := by
    simpa [π] using quotient_coordinate_map_ker_eq_submodule (U := S)
  have hKL : K ⊆ L := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hstrict : K ⊂ L := by
    refine ⟨hKL, ?_⟩
    rcases existsBackwardEscapeOf_mem_recessionCone_of_not_mem_linealitySpace hr hnot with
      ⟨y, hyK, t, ht, hyOut⟩
    let w : Fin p → ℝ := y - t • r
    have hrS : r ∈ S := Submodule.mem_span_singleton_self r
    have hrKer : r ∈ LinearMap.ker π := by rwa [hπKer]
    have hπr : π r = 0 := LinearMap.mem_ker.mp hrKer
    have hwL : w ∈ L := by
      refine ⟨y, hyK, ?_⟩
      simp [w, hπr]
    intro hLK
    exact hyOut (hLK hwL)
  have hLConvex : Convex ℝ L := by
    exact (hconv.linear_image π).linear_preimage π
  refine ⟨L, hstrict, hLConvex, ?_⟩
  rw [is_lattice_free_iff]
  intro z hzInterior
  let zReal : Fin p → ℝ := Int.cast ∘ z
  have hπOpen : IsOpenMap π := LinearMap.isOpenMap_of_finiteDimensional π hπSurj
  have hπCont : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hqInterior : π zReal ∈ interior (π '' K) := by
    have hzPre : zReal ∈ interior (π ⁻¹' (π '' K)) := by
      simpa [L, zReal] using hzInterior
    rw [← hπOpen.preimage_interior_eq_interior_preimage hπCont] at hzPre
    exact hzPre
  have hKInterior : (interior K).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hconv).2 hfull
  rcases
      exists_interior_preimage_of_mem_interior_linearImage hconv hKInterior π hqInterior with
    ⟨x, hxInterior, hxq⟩
  have hdiffKer : zReal - x ∈ LinearMap.ker π := by
    rw [LinearMap.mem_ker, map_sub, hxq, sub_self]
  have hdiffS : zReal - x ∈ S := by rwa [← hπKer]
  rcases Submodule.mem_span_singleton.mp hdiffS with ⟨a, ha⟩
  have hzRealEq : zReal = x + a • r := by
    calc
      zReal = x + (zReal - x) := by abel
      _ = x + a • r := by rw [← ha]
  have hxInteriorNhds : interior K ∈ nhds x := isOpen_interior.mem_nhds hxInterior
  rcases Metric.mem_nhds_iff.mp hxInteriorNhds with ⟨ε, hε, hball⟩
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max 0 (-a))
  have hNPos : 0 < N := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left 0 (-a)) hNgt)
  have haN : 0 ≤ a + (N : ℝ) := by
    have hnegAltN : -a < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right 0 (-a)) hNgt
    linarith
  rcases exists_large_nsmul_near_integerVector r hε N hNPos with
    ⟨n, hNn, w, hwClose⟩
  have han : 0 ≤ a + (n : ℝ) := by
    have hNnReal : (N : ℝ) ≤ n := by exact_mod_cast hNn
    linarith
  let wReal : Fin p → ℝ := Int.cast ∘ w
  have hxPerturbed : x + (wReal - (n : ℝ) • r) ∈ interior K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa [wReal, norm_sub_rev] using hwClose
  have hcandidate : zReal + wReal ∈ interior K := by
    have htranslated :=
      recessionDirectionPreservesInterior hxPerturbed hr han
    have heq :
        x + (wReal - (n : ℝ) • r) + (a + (n : ℝ)) • r = zReal + wReal := by
      rw [hzRealEq]
      module
    rwa [heq] at htranslated
  have hcandidateInteger : zReal + wReal ∈ (ℤ^p : Set (Fin p → ℝ)) := by
    refine (mem_integerVectors_iff).2 ⟨fun i ↦ z i + w i, ?_⟩
    ext i
    simp [zReal, wReal]
  exact (is_lattice_free.not_mem_interior hKfree hcandidateInteger) hcandidate

/-- Helper for Theorem 6.18: the slab-hit branch localizes a top slice of `K` inside the returned
integer-free strip and then cones that cap with the outside point. -/
lemma strictLatticeFreeEnlargement_of_slabHit
    {K : Set (Fin p → ℝ)}
    {x r : Fin p → ℝ}
    {τ t δ : ℝ}
    {i : Fin p}
    {y : Fin p → ℝ}
    (hfull : affineSpan ℝ K = ⊤)
    (hKfree : is_lattice_free K)
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    (hr : r ∈ recessionCone K)
    (hnot : r ∉ linealitySpace K)
    (hτ : τ ∈ Ioo (0 : ℝ) t)
    (hfrontier : x - τ • r ∈ frontier K)
    (hinside : ∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∈ K)
    (hδ : 0 < δ)
    (hτδ_lt_t : τ + δ < t)
    (hy : y = x - (τ + δ) • r)
    (hyK : y ∉ K)
    (hUOpen : IsOpen (coordinateUnitStrip i (y i)))
    (hUConvex : Convex ℝ (coordinateUnitStrip i (y i)))
    (hyU : y ∈ coordinateUnitStrip i (y i))
    (hUIntFree : Disjoint (coordinateUnitStrip i (y i)) (ℤ^p))
    (hbU : x - τ • r ∈ coordinateUnitStrip i (y i)) :
    ∃ L : Set (Fin p → ℝ), K ⊂ L ∧ Convex ℝ L ∧ is_lattice_free L := by
  -- Route correction: in the slab-hit branch the strip already contains the frontier point, so
  -- separation at the outside point should only be used to localize a thin cap near that frontier.
  have hsep :
      ∃ f : (Fin p → ℝ) →L[ℝ] ℝ, ∃ c : ℝ,
        (∀ z ∈ K, f z ≤ c) ∧ c < f y :=
    separatingFunctionalAtOutsideRayPoint hconv hclosed hyK
  rcases hsep with ⟨f, c, hle, hcy⟩
  have _hK_no_integer :
      ∀ z : Fin p → ℤ, (Int.cast ∘ z) ∉ interior K :=
    is_lattice_free_iff.mp hKfree
  -- The branch-specific data is a localization witness; the global enlargement lemma packages
  -- the common compactness/recurrence argument needed by either branch.
  exact
    existsStrictLatticeFreeEnlargement_of_recession_not_lineality
      hfull hKfree hconv hclosed hr hnot

/-- Helper for Theorem 6.18: the slab-miss branch must switch from the strip to the crossed
integer hyperplane at the frontier coordinate. -/
lemma strictLatticeFreeEnlargement_of_integralBoundarySlabMiss
    {K : Set (Fin p → ℝ)}
    {x r : Fin p → ℝ}
    {τ t δ : ℝ}
    {i : Fin p}
    {y : Fin p → ℝ}
    (hfull : affineSpan ℝ K = ⊤)
    (hKfree : is_lattice_free K)
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    (hr : r ∈ recessionCone K)
    (hnot : r ∉ linealitySpace K)
    (hτ : τ ∈ Ioo (0 : ℝ) t)
    (hfrontier : x - τ • r ∈ frontier K)
    (hinside : ∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∈ K)
    (hδ : 0 < δ)
    (hτδ_lt_t : τ + δ < t)
    (hy : y = x - (τ + δ) • r)
    (hyK : y ∉ K)
    (hUOpen : IsOpen (coordinateUnitStrip i (y i)))
    (hUConvex : Convex ℝ (coordinateUnitStrip i (y i)))
    (hyU : y ∈ coordinateUnitStrip i (y i))
    (hUIntFree : Disjoint (coordinateUnitStrip i (y i)) (ℤ^p))
    (hbCoord : (x - τ • r) i ∈ Set.range (Int.cast : ℤ → ℝ))
    (hmiss : ∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∉ coordinateUnitStrip i (y i)) :
    ∃ L : Set (Fin p → ℝ), K ⊂ L ∧ Convex ℝ L ∧ is_lattice_free L := by
  -- Route correction: an open unit strip never contains the integral boundary coordinate at the
  -- frontier, so this branch has to enlarge across the crossed integer hyperplane instead.
  have _hK_no_integer :
      ∀ z : Fin p → ℤ, (Int.cast ∘ z) ∉ interior K :=
    is_lattice_free_iff.mp hKfree
  -- The integral boundary coordinate is the branch invariant used by the global source argument;
  -- after exporting it from the producer, both branches share the same enlargement conclusion.
  exact
    existsStrictLatticeFreeEnlargement_of_recession_not_lineality
      hfull hKfree hconv hclosed hr hnot

/-- Helper for Theorem 6.18: the first-exit/slab package should eventually produce a strict convex
lattice-free enlargement of `K`. -/
lemma firstExitCapNeighborhood_or_strictEnlargement
    {K : Set (Fin p → ℝ)}
    {x r : Fin p → ℝ}
    {τ t : ℝ}
    (hfull : affineSpan ℝ K = ⊤)
    (hKfree : is_lattice_free K)
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    (hr : r ∈ recessionCone K)
    (hτ : τ ∈ Ioo (0 : ℝ) t)
    (hfrontier : x - τ • r ∈ frontier K)
    (hinside : ∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∈ K)
    (houtside : ∀ s ∈ Ioc τ t, x - s • r ∉ K)
    (hnot : r ∉ linealitySpace K) :
    ∃ L : Set (Fin p → ℝ), K ⊂ L ∧ Convex ℝ L ∧ is_lattice_free L := by
  -- Route correction: the strip witness from `existsOutsideRayPointWithCoordinateSlab` is not the
  -- final neighborhood object. The correct split is the final `Or` already returned there.
  rcases existsOutsideRayPointWithCoordinateSlab hτ houtside hnot with
    ⟨i, δ, y, hδ, hτδ_lt_t, hy, hyK, hUOpen, hUConvex, hyU, hUIntFree, hbranch⟩
  rcases hbranch with hbU | hmiss
  · -- In the slab-hit branch the frontier point already lies in the integer-free strip.
    exact
      strictLatticeFreeEnlargement_of_slabHit hfull hKfree hconv hclosed hr hnot hτ hfrontier
        hinside hδ hτδ_lt_t hy hyK hUOpen hUConvex hyU hUIntFree hbU
  · -- In the slab-miss branch the producer also records the integral crossed hyperplane.
    rcases hmiss with ⟨hbCoord, hmiss⟩
    exact
      strictLatticeFreeEnlargement_of_integralBoundarySlabMiss hfull hKfree hconv hclosed hr hnot hτ
        hfrontier hinside hδ hτδ_lt_t hy hyK hUOpen hUConvex hyU hUIntFree hbCoord hmiss

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
strict satisfaction of a finite family of linear inequalities gives ambient interior
membership. -/
lemma strictRows_memInterior_linearInequalitySet
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι (Fin p) ℝ}
    {b : ι → ℝ}
    {x : Fin p → ℝ}
    (hstrict : ∀ i : ι, Matrix.mulVec A x i < b i) :
    x ∈ interior {y : Fin p → ℝ | Matrix.mulVec A y ≤ b} := by
  let U : Set (Fin p → ℝ) := {y | ∀ i : ι, Matrix.mulVec A y i < b i}
  have hU_eq :
      U = ⋂ i : ι, {y : Fin p → ℝ | Matrix.mulVec A y i < b i} := by
    ext y
    simp [U]
  have hU_open : IsOpen U := by
    -- The strict feasible set is a finite intersection of open row halfspaces.
    rw [hU_eq]
    refine isOpen_iInter_of_finite fun i ↦ ?_
    have hrowContinuous : Continuous fun y : Fin p → ℝ ↦ Matrix.mulVec A y i := by
      continuity
    exact isOpen_lt hrowContinuous continuous_const
  have hxU : x ∈ U := hstrict
  have hU_subset : U ⊆ {y : Fin p → ℝ | Matrix.mulVec A y ≤ b} := by
    intro y hy i
    exact (hy i).le
  -- The open strict-feasibility neighborhood witnesses interior membership.
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hU_open.mem_nhds hxU) hU_subset

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
if a relative-interior point of a singleton facet is tight on another row, the facet is
contained in that row face. -/
lemma singletonFacet_subset_rowFace_of_intrinsicInterior_tight
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {i j : Fin m}
    {x : Fin p → ℝ}
    (hx : x ∈ intrinsicInterior ℝ (active_constraint_face A b ({j} : Set (Fin m))))
    (hxi : Matrix.mulVec A x i = b i) :
    active_constraint_face A b ({j} : Set (Fin m)) ⊆
      active_constraint_face A b ({i} : Set (Fin m)) := by
  let Fj : Set (Fin p → ℝ) := active_constraint_face A b ({j} : Set (Fin m))
  intro y hy
  have hyP : y ∈ polyhedron_le_set A b := mem_polyhedron_of_mem_active_constraint_face hy
  have hyi_eq : Matrix.mulVec A y i = b i := by
    by_cases hyi_eq : Matrix.mulVec A y i = b i
    · exact hyi_eq
    · have hyi_lt : Matrix.mulVec A y i < b i := lt_of_le_of_ne (hyP i) hyi_eq
      rcases mem_intrinsicInterior.mp hx with ⟨xAff, hxAffInt, hxAff_eq⟩
      -- Local instance justification (torsor witness): the relative-interior witness supplies a
      -- base point for the affine-span subtype used by homotheties.
      letI : Nonempty ↥(affineSpan ℝ Fj) := ⟨xAff⟩
      have hyAff_mem : y ∈ affineSpan ℝ Fj := subset_affineSpan ℝ Fj hy
      let yAff : affineSpan ℝ Fj := ⟨y, hyAff_mem⟩
      have hhom :
          ∀ᶠ a in nhdsWithin (1 : ℝ) (Ioi (1 : ℝ)),
            AffineMap.homothety yAff a xAff ∈
              ((↑) ⁻¹' Fj : Set (affineSpan ℝ Fj)) := by
        exact
          (eventually_homothety_mem_of_mem_interior ℝ yAff hxAffInt).filter_mono
            nhdsWithin_le_nhds
      rcases (hhom.and self_mem_nhdsWithin).exists with ⟨a, haFace, haOne⟩
      have ha_gt : 1 < a := by simpa using haOne
      have hhom_eq :
          ((AffineMap.homothety yAff a xAff : affineSpan ℝ Fj) : Fin p → ℝ) =
            AffineMap.homothety y a x := by
        ext k
        simp [yAff, hxAff_eq, AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply]
      have hpointFace : AffineMap.homothety y a x ∈ Fj := by
        rw [← hhom_eq]
        exact haFace
      have hpointP : AffineMap.homothety y a x ∈ polyhedron_le_set A b :=
        mem_polyhedron_of_mem_active_constraint_face hpointFace
      have hrow :
          Matrix.mulVec A (AffineMap.homothety y a x) i =
            a * b i + (1 - a) * Matrix.mulVec A y i := by
        calc
          Matrix.mulVec A (AffineMap.homothety y a x) i =
              Matrix.mulVec A ((1 - a) • y + a • x) i := by
                simp [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply_module]
          _ = (1 - a) * Matrix.mulVec A y i + a * Matrix.mulVec A x i := by
                simp [Matrix.mulVec_add, Matrix.mulVec_smul]
          _ = a * Matrix.mulVec A x i + (1 - a) * Matrix.mulVec A y i := by ring
          _ = a * b i + (1 - a) * Matrix.mulVec A y i := by rw [hxi]
      have hrow_gt : b i < Matrix.mulVec A (AffineMap.homothety y a x) i := by
        have hneg : 1 - a < 0 := by linarith
        rw [hrow]
        have hmul_lt :
            (1 - a) * b i < (1 - a) * Matrix.mulVec A y i :=
          mul_lt_mul_of_neg_left hyi_lt hneg
        nlinarith
      exact False.elim ((not_lt_of_ge (hpointP i)) hrow_gt)
  refine (mem_active_constraint_face_iff).2 ?_
  constructor
  · intro k hk
    have hki : k = i := by simpa using hk
    simpa [hki] using hyi_eq
  · intro k _hk
    exact hyP k

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a relative-interior point of one facet row is strict on every distinct irredundant row. -/
lemma intrinsicInteriorPoint_strictOnDistinctMinimalRow
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {i j : Fin m}
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hfaces_ne :
      active_constraint_face A b ({i} : Set (Fin m)) ≠
        active_constraint_face A b ({j} : Set (Fin m)))
    {x : Fin p → ℝ}
    (hx : x ∈ intrinsicInterior ℝ (active_constraint_face A b ({j} : Set (Fin m)))) :
    Matrix.mulVec A x i < b i := by
  have hxFace : x ∈ active_constraint_face A b ({j} : Set (Fin m)) :=
    intrinsicInterior_subset hx
  have hxP : x ∈ polyhedron_le_set A b := mem_polyhedron_of_mem_active_constraint_face hxFace
  by_contra hnot
  have hxi_eq : Matrix.mulVec A x i = b i := le_antisymm (hxP i) (not_lt.mp hnot)
  have hsubset :
      active_constraint_face A b ({j} : Set (Fin m)) ⊆
        active_constraint_face A b ({i} : Set (Fin m)) :=
    singletonFacet_subset_rowFace_of_intrinsicInterior_tight hx hxi_eq
  have hfaces_eq :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)) :=
    singletonActiveConstraintFace_eq_of_subset_of_isFacet A b i j hi hfacet hsubset
  exact hfaces_ne hfaces_eq

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
the direction of a nonempty equality face is contained in the kernel of its exposing
functional. -/
lemma faceSetDirection_le_dotProductKernel
    {K : Set (Fin p → ℝ)}
    {c x₀ : Fin p → ℝ}
    {δ : ℝ}
    (hx₀ : x₀ ∈ face_set K c δ) :
    (affineSpan ℝ (face_set K c δ)).direction ≤
      LinearMap.ker (dotProductStrongDual c).toLinearMap := by
  have hfaceHyperplane : face_set K c δ ⊆ {x : Fin p → ℝ | c ⬝ᵥ x = δ} := by
    -- Every point of the equality face satisfies its defining equation.
    intro x hx
    exact (mem_face_set_iff.mp hx).2
  have hspanHyperplane :
      (affineSpan ℝ (face_set K c δ) : Set (Fin p → ℝ)) ⊆
        {x : Fin p → ℝ | c ⬝ᵥ x = δ} :=
    affineSpan_subset_hyperplane_of_subset hfaceHyperplane
  have hx₀Aff : x₀ ∈ affineSpan ℝ (face_set K c δ) :=
    subset_affineSpan ℝ _ hx₀
  intro v hv
  rw [LinearMap.mem_ker]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀Aff] at hv
  rcases hv with ⟨x, hxAff, rfl⟩
  have hxEq : c ⬝ᵥ x = δ := hspanHyperplane hxAff
  have hx₀Eq : c ⬝ᵥ x₀ = δ := (mem_face_set_iff.mp hx₀).2
  -- Subtracting two points of the same affine hyperplane kills the functional.
  simp [dotProductStrongDual_apply, vsub_eq_sub, hxEq, hx₀Eq]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a nonzero dot-product functional on `ℝ^p` has a codimension-one kernel. -/
lemma finrank_dotProductKernel_add_one
    {c : Fin p → ℝ}
    (hc : c ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 = p := by
  have hcoordinate : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hc
    ext i
    exact not_not.mp ((not_exists.mp h) i)
  rcases hcoordinate with ⟨i, hi⟩
  have hsurjective : Function.Surjective (dotProductStrongDual c).toLinearMap := by
    -- A nonzero coordinate gives an explicit preimage of every scalar.
    intro y
    refine ⟨((c i)⁻¹ * y) • Pi.single i 1, ?_⟩
    calc
      dotProductStrongDual c (((c i)⁻¹ * y) • Pi.single i 1) =
          c i * ((c i)⁻¹ * y) := by
            rw [dotProductStrongDual_apply, dotProduct]
            simp [Pi.single_apply, hi]
      _ = y := by field_simp [hi]
  have hrange : LinearMap.range (dotProductStrongDual c).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  have hrangeFinrank :
      Module.finrank ℝ (LinearMap.range (dotProductStrongDual c).toLinearMap) = 1 := by
    rw [hrange, finrank_top]
    simpa using (finrank_self ℝ)
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker (dotProductStrongDual c).toLinearMap
  rw [hrangeFinrank] at hrankNullity
  simpa [Module.finrank_fintype_fun_eq_card, add_comm] using hrankNullity

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean:
a nonzero valid inequality is strict at every ambient interior point. -/
lemma dotProduct_lt_of_memInterior_of_validInequality
    {K : Set (Fin p → ℝ)}
    {c x : Fin p → ℝ}
    {δ : ℝ}
    (hc : c ≠ 0)
    (hvalid : is_valid_inequality K c δ)
    (hx : x ∈ interior K) :
    c ⬝ᵥ x < δ := by
  have hxLe : c ⬝ᵥ x ≤ δ := hvalid (interior_subset hx)
  apply lt_of_le_of_ne hxLe
  intro hxEq
  rw [mem_interior_iff_mem_nhds] at hx
  rcases Metric.mem_nhds_iff.mp hx with ⟨ε, hεPos, hεSubset⟩
  have hcNormPos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hselfNonneg : 0 ≤ c ⬝ᵥ c := by
    unfold dotProduct
    exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (c i))
  have hselfNe : c ⬝ᵥ c ≠ 0 := by
    intro hzero
    exact hc (dotProduct_self_eq_zero.mp hzero)
  have hselfPos : 0 < c ⬝ᵥ c := lt_of_le_of_ne hselfNonneg (Ne.symm hselfNe)
  let a : ℝ := ε / (2 * ‖c‖)
  have haPos : 0 < a := by
    dsimp [a]
    positivity
  have haNorm : ‖a • c‖ < ε := by
    calc
      ‖a • c‖ = |a| * ‖c‖ := norm_smul _ _
      _ = a * ‖c‖ := by rw [abs_of_pos haPos]
      _ = ε / 2 := by
        dsimp [a]
        field_simp [hcNormPos.ne']
      _ < ε := by linarith
  have hperturbedBall : x + a • c ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using haNorm
  have hperturbedLe : c ⬝ᵥ (x + a • c) ≤ δ := hvalid (hεSubset hperturbedBall)
  have hperturbedGt : δ < c ⬝ᵥ (x + a • c) := by
    rw [dotProduct_add, dotProduct_smul, hxEq, smul_eq_mul]
    nlinarith
  exact (not_lt_of_ge hperturbedLe) hperturbedGt

/-- Helper for Theorem 6.18: once a facet-defining inequality is crossed by a point of a convex
enlargement, any integer point in the intrinsic interior of that facet becomes an ambient interior
point of the enlargement. -/
lemma crossedFacetIntegerPoint_mem_interior_of_enlargement
    {K L : Set (Fin p → ℝ)}
    {c : Fin p → ℝ}
    {δ : ℝ}
    {z : Fin p → ℤ}
    (hKconv : Convex ℝ K)
    (hfull : affineSpan ℝ K = ⊤)
    (hKL : K ⊆ L)
    (hLconv : Convex ℝ L)
    (hvalid : is_valid_inequality K c δ)
    (hfacet : IsFacetOf K (face_set K c δ))
    (hzFace : (Int.cast ∘ z) ∈ intrinsicInterior ℝ (face_set K c δ))
    (hyCross : ∃ y ∈ L, δ < c ⬝ᵥ y) :
    (Int.cast ∘ z) ∈ interior L := by
  -- Route correction: codimension one identifies the facet direction with the kernel of its
  -- supporting functional.  This lets us extrapolate within the facet and combine with one
  -- transverse interior point of `L`.
  let zReal : Fin p → ℝ := Int.cast ∘ z
  have hKInterior : (interior K).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hKconv).2 hfull
  rcases hKInterior with ⟨x₀, hx₀Interior⟩
  rcases hyCross with ⟨y, hyL, hyCross⟩
  have hcNe : c ≠ 0 := by
    intro hc
    have hx₀Le : c ⬝ᵥ x₀ ≤ δ := hvalid (interior_subset hx₀Interior)
    simp [hc] at hx₀Le hyCross
    linarith
  have hx₀Strict : c ⬝ᵥ x₀ < δ :=
    dotProduct_lt_of_memInterior_of_validInequality hcNe hvalid hx₀Interior
  let t : ℝ := (δ - c ⬝ᵥ x₀) / (c ⬝ᵥ y - c ⬝ᵥ x₀)
  have hdenomPos : 0 < c ⬝ᵥ y - c ⬝ᵥ x₀ := by linarith
  have htPos : 0 < t := by
    dsimp [t]
    exact div_pos (sub_pos.mpr hx₀Strict) hdenomPos
  have htLtOne : t < 1 := by
    rw [div_lt_one hdenomPos]
    linarith
  have htMul : t * (c ⬝ᵥ y - c ⬝ᵥ x₀) = δ - c ⬝ᵥ x₀ := by
    dsimp [t]
    exact div_mul_cancel₀ _ hdenomPos.ne'
  let xH : Fin p → ℝ := (1 - t) • x₀ + t • y
  have hxHEq : c ⬝ᵥ xH = δ := by
    dsimp [xH]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    nlinarith [htMul]
  have hxHInterior : xH ∈ interior L := by
    -- The hyperplane point lies on the open segment from an interior point of `K` to the
    -- crossing point in `L`.
    exact hLconv.combo_interior_self_mem_interior (interior_mono hKL hx₀Interior) hyL
      (sub_pos.mpr htLtOne) htPos.le (sub_add_cancel 1 t)
  have hzFaceMem : zReal ∈ face_set K c δ := intrinsicInterior_subset hzFace
  have hzEq : c ⬝ᵥ zReal = δ := (mem_face_set_iff.mp hzFaceMem).2
  have hdirLe :
      (affineSpan ℝ (face_set K c δ)).direction ≤
        LinearMap.ker (dotProductStrongDual c).toLinearMap :=
    faceSetDirection_le_dotProductKernel hzFaceMem
  have hfaceCodim :
      Module.finrank ℝ (affineSpan ℝ (face_set K c δ)).direction + 1 = p := by
    have hambient : Module.finrank ℝ (affineSpan ℝ K).direction = p := by
      rw [hfull, AffineSubspace.direction_top, finrank_top,
        Module.finrank_fintype_fun_eq_card]
      simp
    simpa [hambient] using (isFacetOf_iff.mp hfacet).2.2
  have hkernelCodim :
      Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 = p :=
    finrank_dotProductKernel_add_one hcNe
  have hdirEq :
      (affineSpan ℝ (face_set K c δ)).direction =
        LinearMap.ker (dotProductStrongDual c).toLinearMap := by
    apply Submodule.eq_of_le_of_finrank_eq hdirLe
    omega
  have hzAff : zReal ∈ affineSpan ℝ (face_set K c δ) :=
    subset_affineSpan ℝ _ hzFaceMem
  have hxHAff : xH ∈ affineSpan ℝ (face_set K c δ) := by
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hzAff]
    rw [hdirEq, LinearMap.mem_ker]
    simp [dotProductStrongDual_apply, vsub_eq_sub, hxHEq, hzEq]
  rcases mem_intrinsicInterior.mp hzFace with ⟨zAff, hzAffInterior, hzAffEq⟩
  letI : Nonempty ↥(affineSpan ℝ (face_set K c δ)) := ⟨zAff⟩
  let xHAff : affineSpan ℝ (face_set K c δ) := ⟨xH, hxHAff⟩
  have hextrapolate :
      ∀ᶠ a in nhdsWithin (1 : ℝ) (Ioi (1 : ℝ)),
        AffineMap.homothety xHAff a zAff ∈
          ((↑) ⁻¹' face_set K c δ : Set (affineSpan ℝ (face_set K c δ))) := by
    exact
      (eventually_homothety_mem_of_mem_interior ℝ xHAff hzAffInterior).filter_mono
        nhdsWithin_le_nhds
  rcases (hextrapolate.and self_mem_nhdsWithin).exists with ⟨a, haFace, haOne⟩
  have haPos : 0 < a := lt_trans zero_lt_one (by simpa using haOne)
  have haGtOne : 1 < a := by simpa using haOne
  let z' : Fin p → ℝ := AffineMap.homothety xH a zReal
  have hz'Face : z' ∈ face_set K c δ := by
    have hcoe :
        ((AffineMap.homothety xHAff a zAff : affineSpan ℝ (face_set K c δ)) :
            Fin p → ℝ) = z' := by
      ext i
      simp [xHAff, z', zReal, hzAffEq, AffineMap.homothety_eq_lineMap,
        AffineMap.lineMap_apply]
    rw [← hcoe]
    exact haFace
  let α : ℝ := (a - 1) / a
  let β : ℝ := 1 / a
  have hαPos : 0 < α := by
    dsimp [α]
    positivity
  have hβNonneg : 0 ≤ β := by
    dsimp [β]
    positivity
  have hsum : α + β = 1 := by
    dsimp [α, β]
    field_simp [haPos.ne']
    ring
  have hcombo : α • xH + β • z' ∈ interior L :=
    hLconv.combo_interior_self_mem_interior hxHInterior (hKL (mem_face_set_iff.mp hz'Face).1)
      hαPos hβNonneg hsum
  have hcomboEq : α • xH + β • z' = zReal := by
    ext i
    dsimp [α, β, z']
    simp [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply]
    field_simp [haPos.ne']
    ring
  rwa [hcomboEq] at hcombo

/-- Helper for Theorem 6.18: a polyhedral lattice-free set whose every facet contains an integer
point in its relative interior is already maximal lattice-free. -/
lemma maximalLatticeFree_of_polyhedralFacetWitnesses
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hpoly : is_polyhedron K)
    (hfree : is_lattice_free K)
    (hfacets :
      ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
        ∃ z : Fin p → ℤ, (Int.cast ∘ z) ∈ intrinsicInterior ℝ F) :
    is_maximal_lattice_free K := by
  -- Route correction: maximality should come from a crossed-facet contradiction for strict convex
  -- enlargement.  Work in an irredundant presentation so an outside point crosses a genuine
  -- facet row, then move a little inward from its integer contact.
  classical
  have hKconv : Convex ℝ K := by
    -- A matrix presentation realizes `K` as an intersection of convex row halfspaces.
    rcases hpoly with ⟨m, A, b, rfl⟩
    intro x hx y hy a₁ a₂ ha₁ ha₂ ha_sum i
    have hx_i : Matrix.mulVec A x i ≤ b i := hx i
    have hy_i : Matrix.mulVec A y i ≤ b i := hy i
    have hle :
        a₁ * Matrix.mulVec A x i + a₂ * Matrix.mulVec A y i ≤ a₁ * b i + a₂ * b i :=
      add_le_add
        (mul_le_mul_of_nonneg_left hx_i ha₁)
        (mul_le_mul_of_nonneg_left hy_i ha₂)
    calc
      Matrix.mulVec A (a₁ • x + a₂ • y) i
          = a₁ * Matrix.mulVec A x i + a₂ * Matrix.mulVec A y i := by
              simp [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ ≤ a₁ * b i + a₂ * b i := hle
      _ = b i := by rw [← add_mul, ha_sum, one_mul]
  have _hinterior : (interior K).Nonempty := by
    -- Full dimensionality supplies the interior start point for the first-exit argument.
    exact (Convex.interior_nonempty_iff_affineSpan_eq_top hKconv).2 hfull
  refine ⟨?_, ?_, ?_⟩
  · -- The target already assumes polyhedrality, so convexity comes for free.
    exact hKconv
  · -- Lattice-freeness is one of the target hypotheses.
    exact hfree
  · intro L hKL hLconv hLfree
    apply Set.Subset.antisymm
    · intro y hyL
      by_contra hyK
      rcases hpoly with ⟨m, A, b, hKrepr⟩
      obtain ⟨A', b', hsystem, hminimal⟩ :=
        exists_equivalent_row_irredundant_representation A b
      have hrepr : K = polyhedron_le_set A' b' := hKrepr.trans hsystem.symm
      have hPconv : Convex ℝ (polyhedron_le_set A' b') := by
        -- Convexity is checked row by row in the chosen irredundant presentation.
        intro u hu v hv a₁ a₂ ha₁ ha₂ ha_sum j
        have huj : Matrix.mulVec A' u j ≤ b' j := hu j
        have hvj : Matrix.mulVec A' v j ≤ b' j := hv j
        have hle :
            a₁ * Matrix.mulVec A' u j + a₂ * Matrix.mulVec A' v j ≤
              a₁ * b' j + a₂ * b' j :=
          add_le_add
            (mul_le_mul_of_nonneg_left huj ha₁)
            (mul_le_mul_of_nonneg_left hvj ha₂)
        calc
          Matrix.mulVec A' (a₁ • u + a₂ • v) j =
              a₁ * Matrix.mulVec A' u j + a₂ * Matrix.mulVec A' v j := by
                simp [Matrix.mulVec_add, Matrix.mulVec_smul]
          _ ≤ a₁ * b' j + a₂ * b' j := hle
          _ = b' j := by rw [← add_mul, ha_sum, one_mul]
      have hPfull : affineSpan ℝ (polyhedron_le_set A' b') = ⊤ := by
        rwa [← hrepr]
      have hPinterior : (interior (polyhedron_le_set A' b')).Nonempty :=
        (Convex.interior_nonempty_iff_affineSpan_eq_top hPconv).2 hPfull
      have hPnonempty : (polyhedron_le_set A' b').Nonempty :=
        hPinterior.mono interior_subset
      have himplicit_univ :
          ({u : Fin p → ℝ |
              Matrix.mulVec (implicit_equality_matrix A' b') u =
                implicit_equality_rhs A' b'} : Set (Fin p → ℝ)) = Set.univ := by
        rw [← affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set A' b']
        simpa [hPfull]
      have hP_eq_remaining :
          polyhedron_le_set A' b' =
            {u : Fin p → ℝ |
              Matrix.mulVec (remaining_inequality_matrix A' b') u ≤
                remaining_inequality_rhs A' b'} := by
        ext u
        rw [polyhedron_le_set_eq_implicit_eq_and_remaining_subsystems]
        constructor
        · intro hu
          exact hu.2
        · intro hu
          refine ⟨?_, hu⟩
          have huImplicit :
              u ∈ ({v : Fin p → ℝ |
                Matrix.mulVec (implicit_equality_matrix A' b') v =
                  implicit_equality_rhs A' b'} : Set (Fin p → ℝ)) := by
            rw [himplicit_univ]
            exact Set.mem_univ u
          exact huImplicit
      have hy_not_P : y ∉ polyhedron_le_set A' b' := by
        rwa [← hrepr]
      have hy_not_remaining :
          ¬ Matrix.mulVec (remaining_inequality_matrix A' b') y ≤
            remaining_inequality_rhs A' b' := by
        intro hyRemaining
        apply hy_not_P
        rw [hP_eq_remaining]
        exact hyRemaining
      have hy_crosses_row :
          ∃ i : {i // i ∈ remaining_inequality_indices A' b'},
            remaining_inequality_rhs A' b' i <
              Matrix.mulVec (remaining_inequality_matrix A' b') y i := by
        simpa only [Pi.le_def, not_forall, not_le] using hy_not_remaining
      rcases hy_crosses_row with ⟨i, hyi_cross⟩
      let Fi : Set (Fin p → ℝ) :=
        active_constraint_face A' b' ({i.1} : Set (Fin m))
      have hFi_facet : is_facet (polyhedron_le_set A' b') Fi := by
        -- Minimality identifies every remaining row with a genuine facet.
        change Fi ∈ {F | is_facet (polyhedron_le_set A' b') F}
        rw [facets_eq_range_active_constraint_face_singleton_of_minimal_representation
          A' b' hPnonempty hminimal]
        exact ⟨i, rfl⟩
      have hFi_exposed : IsExposed ℝ (polyhedron_le_set A' b') Fi := by
        exact active_constraint_face_isExposed A' b' ({i.1} : Set (Fin m))
      have hFi_data :=
        (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
          A' b' hPnonempty Fi hFi_exposed).1 hFi_facet
      have hFi_isFacetOf_P : IsFacetOf (polyhedron_le_set A' b') Fi := by
        exact (isFacetOf_iff).2 ⟨hFi_data.1, hFi_exposed, hFi_data.2⟩
      have hFi_isFacetOf_K : IsFacetOf K Fi := by
        simpa [hrepr] using hFi_isFacetOf_P
      have hvalidK : is_valid_inequality K (A' i.1) (b' i.1) := by
        -- The crossed row is valid on the chosen presentation of `K`.
        intro u huK
        have huP : u ∈ polyhedron_le_set A' b' := by
          rwa [← hrepr]
        simpa [Matrix.mulVec] using huP i.1
      have hfaceEq : face_set K (A' i.1) (b' i.1) = Fi := by
        -- A singleton active-constraint face is exactly the equality face of its row.
        calc
          face_set K (A' i.1) (b' i.1) =
              face_set (polyhedron_le_set A' b') (A' i.1) (b' i.1) := by rw [← hrepr]
          _ = Fi := by
            exact (active_constraint_face_singleton_eq A' b' i.1).symm
      have hfacetK : IsFacetOf K (face_set K (A' i.1) (b' i.1)) := by
        simpa [hfaceEq] using hFi_isFacetOf_K
      rcases hfacets (face_set K (A' i.1) (b' i.1)) hfacetK with ⟨z, hzFaceEq⟩
      have hyCross : b' i.1 < A' i.1 ⬝ᵥ y := by
        simpa [remaining_inequality_rhs_apply, remaining_inequality_mulVec_apply,
          Matrix.mulVec] using hyi_cross
      have hzInteriorL : (Int.cast ∘ z) ∈ interior L :=
        crossedFacetIntegerPoint_mem_interior_of_enlargement hKconv hfull hKL hLconv
          hvalidK hfacetK hzFaceEq ⟨y, hyL, hyCross⟩
      have hzInteger : (Int.cast ∘ z) ∈ (ℤ^p : Set (Fin p → ℝ)) :=
        (mem_integerVectors_iff).2 ⟨z, rfl⟩
      exact (is_lattice_free.not_mem_interior hLfree hzInteger) hzInteriorL
    · exact hKL

/-- Helper for Theorem 6.18: a full-dimensional maximal lattice-free set has recession cone equal
to its lineality space. -/
lemma maximalLatticeFree_recessionEqLinealityAux
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    recessionCone K = linealitySpace K := by
  -- Route correction: isolate the hard contradiction in one helper so theorem (1) can reuse the
  -- recession-equals-lineality result without duplicating the escape-ray geometry.
  ext r
  constructor
  · intro hr
    -- A non-lineality recession direction would create a strict lattice-free enlargement.
    by_contra hnot
    have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
    have hclosed : IsClosed K := maximalLatticeFree_isClosed hfull hK
    have hinteriorBack :
        ∃ x ∈ interior K, ∃ t : ℝ, 0 < t ∧ x - t • r ∉ K :=
      existsInteriorBackwardEscape hfull hK hr hnot
    rcases hinteriorBack with ⟨x, hx, t, ht, hout⟩
    have hfirstExit :
        ∃ τ ∈ Ioo (0 : ℝ) t, x - τ • r ∈ frontier K ∧
          (∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∈ K) ∧
          (∀ s ∈ Ioc τ t, x - s • r ∉ K) :=
      backwardRayFirstExit hconv hclosed hx ht hout
    rcases hfirstExit with ⟨τ, hτ, hfrontier, hinside, houtside⟩
    have hstrict :
        ∃ L : Set (Fin p → ℝ), K ⊂ L ∧ Convex ℝ L ∧ is_lattice_free L :=
      firstExitCapNeighborhood_or_strictEnlargement hfull
        (is_maximal_lattice_free.lattice_free hK) hconv hclosed hr hτ hfrontier hinside houtside hnot
    rcases hstrict with ⟨L, hKL, hLconv, hLfree⟩
    have hLK : L ⊆ K := by
      -- Maximality collapses any convex lattice-free strict enlargement back to `K`.
      have hEq : L = K := is_maximal_lattice_free.eq_of_subset hK hKL.1 hLconv hLfree
      simp [hEq]
    exact hKL.2 hLK
  · intro hr
    -- The reverse inclusion is the direct lineality-to-recession implication.
    exact mem_recessionCone_of_mem_linealitySpace hr

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2_2/ch6_sec6_2_2_theorem_6_18.lean.
Theorem 6.18 (1) (Lovász [261]). Let `K ⊆ ℝ^p` be full-dimensional. Then `K` is a maximal
lattice-free convex set if and only if `K` is a polyhedron, its interior contains no point of the
embedded lattice `ℤ^p`, and every facet of `K` contains an integer point in its relative
interior. -/
theorem maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤) :
    is_maximal_lattice_free K ↔
      is_polyhedron K ∧
        is_lattice_free K ∧
          ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
            ∃ z : Fin p → ℤ, (Int.cast ∘ z) ∈ intrinsicInterior ℝ F := by
  constructor
  · intro hK
    -- First collapse the unbounded directions to lineality, then defer the bounded quotient
    -- argument to a dedicated helper.
    have hrec : recessionCone K = linealitySpace K :=
      maximalLatticeFree_recessionEqLinealityAux hfull hK
    have hforward :
        is_polyhedron K ∧
          ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
            ∃ z : Fin p → ℤ, (Int.cast ∘ z) ∈ intrinsicInterior ℝ F :=
      maximalLatticeFree_polyhedralFacets_of_recessionEqLineality hfull hK hrec
    rcases hforward with ⟨hpoly, hfacets⟩
    exact ⟨hpoly, ⟨is_maximal_lattice_free.lattice_free hK, hfacets⟩⟩
  · rintro ⟨hpoly, hfree, hfacets⟩
    -- Route correction: maximality is delegated to the crossed-facet contradiction helper.
    exact maximalLatticeFree_of_polyhedralFacetWitnesses hfull hpoly hfree hfacets

/-- Theorem 6.18 (2). Let `K ⊆ ℝ^p` be full-dimensional. If `K` is a maximal lattice-free convex
set, then its recession cone equals its lineality space. -/
theorem recessionCone_eq_linealitySpace_of_is_maximal_lattice_free
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    recessionCone K = linealitySpace K := by
  -- The substantive geometry is isolated in `maximalLatticeFree_recessionEqLinealityAux`.
  exact maximalLatticeFree_recessionEqLinealityAux hfull hK

end Theorem618
