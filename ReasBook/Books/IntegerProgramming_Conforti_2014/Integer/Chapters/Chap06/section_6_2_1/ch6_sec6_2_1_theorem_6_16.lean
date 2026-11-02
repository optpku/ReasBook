import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_lemma_6_15

open Set
open scoped Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

section Theorem616

variable {n : ℕ} {g : (Fin n → ℝ) → ℝ}

/-- The unit sublevel set `K = {r : ℝ^n | g r ≤ 1}` attached to `g : ℝ^n → ℝ`. -/
def sublinear_unit_sublevel_set (g : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {r | g r ≤ 1}

/-- Membership in `sublinear_unit_sublevel_set g` is exactly the defining inequality `g r ≤ 1`. -/
theorem mem_sublinear_unit_sublevel_set {r : Fin n → ℝ} :
    r ∈ sublinear_unit_sublevel_set g ↔ g r ≤ 1 :=
  Iff.rfl

namespace Function.Sublinear

/-- Theorem 6.16 (1). For a sublinear function `g : ℝ^n → ℝ`, the unit sublevel set
`K = {r : ℝ^n | g r ≤ 1}` is closed. The source nonnegativity assumption is redundant here. -/
theorem isClosed_unitSublevelSet (hg : g.Sublinear) :
    IsClosed (sublinear_unit_sublevel_set g) := by
  change IsClosed (g ⁻¹' Set.Iic (1 : ℝ))
  exact isClosed_Iic.preimage hg.continuous

/-- Theorem 6.16 (2). For a sublinear function `g : ℝ^n → ℝ`, the unit sublevel set
`K = {r : ℝ^n | g r ≤ 1}` is convex. The source nonnegativity assumption is redundant here. -/
theorem convex_unitSublevelSet (hg : g.Sublinear) :
    Convex ℝ (sublinear_unit_sublevel_set g) := by
  simpa [sublinear_unit_sublevel_set] using hg.convexOn_univ.convex_le (1 : ℝ)

/-- Theorem 6.16 (3). For a sublinear function `g : ℝ^n → ℝ`, the origin belongs to the interior
of the unit sublevel set `K = {r : ℝ^n | g r ≤ 1}`. The source nonnegativity assumption is
redundant here. -/
theorem zero_mem_interior_unitSublevelSet (hg : g.Sublinear) :
    (0 : Fin n → ℝ) ∈ interior (sublinear_unit_sublevel_set g) := by
  have hcont0 : ContinuousAt g (0 : Fin n → ℝ) := hg.continuous.continuousAt
  have hlt : g ⁻¹' Set.Iio (1 : ℝ) ∈ nhds (0 : Fin n → ℝ) := by
    exact hcont0.preimage_mem_nhds <| isOpen_Iio.mem_nhds <| by
      simp [hg.map_zero]
  have hsubset : g ⁻¹' Set.Iio (1 : ℝ) ⊆ sublinear_unit_sublevel_set g := by
    intro r hr
    simpa [sublinear_unit_sublevel_set] using hr.le
  have hnhds : sublinear_unit_sublevel_set g ∈ nhds (0 : Fin n → ℝ) :=
    Filter.mem_of_superset hlt hsubset
  exact mem_interior_iff_mem_nhds.2 hnhds

/-- Theorem 6.16 (4). If `g : ℝ^n → ℝ` is nonnegative and sublinear, then the unit sublevel set
`K = {r : ℝ^n | g r ≤ 1}` has gauge `γ_K = g`. -/
theorem gauge_unitSublevelSet_eq
    (hg : g.Sublinear)
    (hg_nonneg : ∀ r : Fin n → ℝ, 0 ≤ g r)
    (r : Fin n → ℝ) :
    gauge (sublinear_unit_sublevel_set g) r = g r := by
  let K : Set (Fin n → ℝ) := sublinear_unit_sublevel_set g
  have hK_zero : (0 : Fin n → ℝ) ∈ interior K := by
    simpa [K] using hg.zero_mem_interior_unitSublevelSet
  have hK_nonempty :
      {t : ℝ | t ∈ Set.Ioi (0 : ℝ) ∧ t⁻¹ • r ∈ K}.Nonempty := by
    rcases exists_pos_smul_mem_of_zero_mem_interior hK_zero r with ⟨t, ht, hr⟩
    refine ⟨t, ht, ?_⟩
    rwa [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne'] at hr
  have hK_lower : g r ≤ gauge K r := by
    rw [gauge_def']
    exact le_csInf hK_nonempty fun t ht ↦ by
      have ht_mem : g (t⁻¹ • r) ≤ 1 := by
        simpa [K, sublinear_unit_sublevel_set] using ht.2
      calc
        g r = g (t • (t⁻¹ • r)) := by rw [smul_inv_smul₀ ht.1.ne']
        _ = t * g (t⁻¹ • r) := hg.positivelyHomogeneous _ t ht.1
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left ht_mem ht.1.le
        _ = t := by ring
  have hK_upper : gauge K r ≤ g r := by
    by_cases hgr_zero : g r = 0
    · have hgauge_le_zero : gauge K r ≤ 0 := by
        refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
        have hhalf : gauge K r ≤ ε / 2 := by
          refine gauge_le_of_mem (by positivity) ?_
          rw [Set.mem_smul_set_iff_inv_smul_mem₀ (half_pos hε).ne']
          have hmem : g (((ε / 2 : ℝ)⁻¹) • r) ≤ 1 := by
            calc
              g (((ε / 2 : ℝ)⁻¹) • r) = ((ε / 2 : ℝ)⁻¹) * g r :=
                hg.positivelyHomogeneous _ _ (inv_pos.2 (half_pos hε))
              _ = 0 := by rw [hgr_zero, mul_zero]
              _ ≤ 1 := by norm_num
          simpa [K, sublinear_unit_sublevel_set] using hmem
        linarith
      rw [hgr_zero]
      exact hgauge_le_zero
    · have hgr_pos : 0 < g r := lt_of_le_of_ne (hg_nonneg r) <| by
        simpa [eq_comm] using hgr_zero
      have hr_mem : r ∈ g r • K := by
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ hgr_pos.ne']
        change g ((g r)⁻¹ • r) ≤ 1
        rw [hg.positivelyHomogeneous _ _ (inv_pos.2 hgr_pos)]
        rw [inv_mul_cancel₀ hgr_pos.ne']
      exact gauge_le_of_mem (hg_nonneg r) hr_mem
  exact le_antisymm hK_upper hK_lower

end Function.Sublinear

/-- Theorem 6.16 (1). Let `g : ℝ^n → ℝ` be sublinear and let
`K := {r : ℝ^n | g r ≤ 1}`. Then `K` is closed. -/
theorem isClosed_sublinear_unit_sublevel_set
    (hg_sublinear : g.Sublinear) :
    IsClosed (sublinear_unit_sublevel_set g) :=
  hg_sublinear.isClosed_unitSublevelSet

/-- Theorem 6.16 (2). Let `g : ℝ^n → ℝ` be sublinear and let
`K := {r : ℝ^n | g r ≤ 1}`. Then `K` is convex. -/
theorem convex_sublinear_unit_sublevel_set
    (hg_sublinear : g.Sublinear) :
    Convex ℝ (sublinear_unit_sublevel_set g) :=
  hg_sublinear.convex_unitSublevelSet

/-- Theorem 6.16 (3). Let `g : ℝ^n → ℝ` be sublinear and let
`K := {r : ℝ^n | g r ≤ 1}`. Then the origin belongs to the interior of `K`. -/
theorem zero_mem_interior_sublinear_unit_sublevel_set
    (hg_sublinear : g.Sublinear) :
    (0 : Fin n → ℝ) ∈ interior (sublinear_unit_sublevel_set g) :=
  hg_sublinear.zero_mem_interior_unitSublevelSet

/-- Theorem 6.16 (4). Let `g : ℝ^n → ℝ` be a nonnegative sublinear function and let
`K := {r : ℝ^n | g r ≤ 1}`. Then `g` is the gauge of `K`, i.e. `γ_K(r) = g(r)` for every
`r : ℝ^n`. -/
theorem gauge_sublinear_unit_sublevel_set_eq
    (hg_sublinear : g.Sublinear)
    (hg_nonneg : ∀ r : Fin n → ℝ, 0 ≤ g r)
    (r : Fin n → ℝ) :
    gauge (sublinear_unit_sublevel_set g) r = g r :=
  hg_sublinear.gauge_unitSublevelSet_eq hg_nonneg r

end Theorem616
