import Mathlib.Analysis.Convex.Gauge

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

-- Semantic recall note: no deferred semantic search tool such as `lean_leansearch` was available
-- in this environment. Mathlib already provides the gauge/Minkowski functional as `gauge`; the
-- source-specific statements below use the local analogue theorems
-- `gauge_le_one_iff_mem_closure` and `gauge_lt_one_iff_mem_interior`.

section Definition621Extra1

variable {p : ℕ}

/- Definition 6.2.1-extra-1. The textbook gauge function `γ_K` is mathlib's canonical
`gauge K`; see `gauge_def'` for the equivalent infimum formula
`gauge K r = sInf {t ∈ Set.Ioi (0 : ℝ) | t⁻¹ • r ∈ K}`. -/

/-- Definition 6.2.1-extra-1 (1). If `K ⊆ ℝ^p` contains the origin in its interior, then for every
`r` there exists `t > 0` with `r ∈ t • K`. This is the source-level finiteness condition behind the
gauge of `K`; mathematically, it is the singleton case of the canonical absorbency API. -/
theorem exists_pos_smul_mem_of_zero_mem_interior
    {K : Set (Fin p → ℝ)} (hK_zero : (0 : Fin p → ℝ) ∈ interior K) (r : Fin p → ℝ) :
    ∃ t : ℝ, 0 < t ∧ r ∈ t • K := by
  have hK_nhds : K ∈ nhds (0 : Fin p → ℝ) := mem_interior_iff_mem_nhds.1 hK_zero
  have hK_abs : Absorbent ℝ K := absorbent_nhds_zero hK_nhds
  have hK_nonempty : {t : ℝ | 0 < t ∧ r ∈ t • K}.Nonempty := hK_abs.gauge_set_nonempty
  simpa [Set.nonempty_def] using hK_nonempty

/-- Companion to Definition 6.2.1-extra-1 (2). For a convex set `K ⊆ ℝ^p` with the origin in its
interior, the gauge satisfies `gauge K r < 1` if and only if `r` lies in the interior of `K`. -/
theorem gauge_lt_one_iff_mem_interior_of_convex_of_zero_mem_interior
    {K : Set (Fin p → ℝ)} (hK_convex : Convex ℝ K)
    (hK_zero : (0 : Fin p → ℝ) ∈ interior K) {r : Fin p → ℝ} :
    gauge K r < 1 ↔ r ∈ interior K := by
  have hK_nhds : K ∈ nhds (0 : Fin p → ℝ) := mem_interior_iff_mem_nhds.1 hK_zero
  rw [gauge_lt_one_iff_mem_interior hK_convex hK_nhds]

/-- Definition 6.2.1-extra-1 (2). For a closed convex set `K ⊆ ℝ^p` with the origin in its
interior, the gauge satisfies `gauge K r ≤ 1` if and only if `r ∈ K`. -/
theorem gauge_le_one_iff_mem_of_isClosed_of_convex_of_zero_mem_interior
    {K : Set (Fin p → ℝ)} (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_zero : (0 : Fin p → ℝ) ∈ interior K) {r : Fin p → ℝ} :
    gauge K r ≤ 1 ↔ r ∈ K := by
  have hK_nhds : K ∈ nhds (0 : Fin p → ℝ) := mem_interior_iff_mem_nhds.1 hK_zero
  rw [gauge_le_one_iff_mem_closure hK_convex hK_nhds, hK_closed.closure_eq]

end Definition621Extra1
