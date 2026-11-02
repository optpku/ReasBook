import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain sampling for this claim:
* primary domain: convex geometry of a real module cut by a linear-functional halfspace;
* core/canonical owners: `convexHull ℝ`, `LinearMap.image_convexHull`, and set preimages under
  `gamma`;
* source-facing layer: the equality between the boundary slice of `convexHull ℝ A` and the convex
  hull of the boundary points of `A`.
-/

/-- Helper for Claim 5.4.1-extra-1: the convex hull of the points of `A` already lying on the
hyperplane `gamma = gamma0` stays inside the corresponding slice of `convexHull ℝ A`. -/
lemma convexHull_subset_inter_hyperplane_of_subset
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : Set E)
    (gamma : E →ₗ[ℝ] ℝ)
    (gamma0 : ℝ) :
    convexHull ℝ (A ∩ gamma ⁻¹' {gamma0}) ⊆ convexHull ℝ A ∩ gamma ⁻¹' {gamma0} := by
  -- The target slice is convex and already contains every generator from `A ∩ H`.
  refine convexHull_min ?_ ?_
  · intro x hx
    exact ⟨subset_convexHull ℝ A hx.1, hx.2⟩
  · exact (convex_convexHull ℝ A).inter ((convex_singleton gamma0).linear_preimage gamma)

/-- Helper for Claim 5.4.1-extra-1: if a convex combination of values bounded above by `c`
already equals `c`, then every positive-weight term must itself equal `c`. -/
lemma eq_of_weighted_sum_eq_of_nonneg_of_le
    {ι : Type*}
    (t : Finset ι)
    (w f : ι → ℝ)
    (c : ℝ)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hf : ∀ i ∈ t, f i ≤ c)
    (hsum : ∑ i ∈ t, w i * f i = c) :
    ∀ i ∈ t, w i ≠ 0 → f i = c := by
  intro i hi hwi
  -- The nonnegative deficits `w i * (c - f i)` sum to zero, so each one vanishes.
  have hsum_zero : ∑ j ∈ t, w j * (c - f j) = 0 := by
    calc
      ∑ j ∈ t, w j * (c - f j)
          = ∑ j ∈ t, (w j * c - w j * f j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (∑ j ∈ t, w j * c) - ∑ j ∈ t, w j * f j := by
            rw [Finset.sum_sub_distrib]
      _ = c - c := by
            rw [← Finset.sum_mul, hw₁, one_mul, hsum]
      _ = 0 := by ring
  have hterm_zero :
      ∀ j ∈ t, w j * (c - f j) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum_zero
    intro j hj
    exact mul_nonneg (hw₀ j hj) (sub_nonneg.mpr (hf j hj))
  have hfactor_zero : c - f i = 0 := by
    rcases mul_eq_zero.mp (hterm_zero i hi) with hwi_zero | hfactor_zero
    · exact False.elim (hwi hwi_zero)
    · exact hfactor_zero
  linarith

/-- Helper for Claim 5.4.1-extra-1: every positive-weight support point in a center-of-mass
representation of a boundary point already lies in the boundary slice `A ∩ (gamma = gamma0)`. -/
lemma support_mem_hyperplane_of_centerMass_eq
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {ι : Type*}
    (A : Set E)
    (gamma : E →ₗ[ℝ] ℝ)
    (gamma0 : ℝ)
    (hA : A ⊆ gamma ⁻¹' Set.Iic gamma0)
    (t : Finset ι)
    (w : ι → ℝ)
    (z : ι → E)
    (x : E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ A)
    (hx : ∑ i ∈ t, w i • z i = x)
    (hxH : gamma x = gamma0) :
    ∀ i ∈ {i ∈ t | w i ≠ 0}, z i ∈ A ∩ gamma ⁻¹' {gamma0} := by
  classical
  -- Applying `gamma` to the weighted-sum equality turns the geometric claim into a scalar one.
  have hle : ∀ i ∈ t, gamma (z i) ≤ gamma0 := by
    intro i hi
    simpa using hA (hz i hi)
  have hgamma_sum : ∑ i ∈ t, w i * gamma (z i) = gamma0 := by
    have hx_gamma : gamma (∑ i ∈ t, w i • z i) = gamma0 := by
      simpa [hx] using hxH
    simpa using hx_gamma
  have hboundary :
      ∀ i ∈ t, w i ≠ 0 → gamma (z i) = gamma0 :=
    eq_of_weighted_sum_eq_of_nonneg_of_le t w (fun i ↦ gamma (z i)) gamma0 hw₀ hw₁ hle hgamma_sum
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hit, hwi⟩
  -- Positive-weight support points stay in `A`, and the scalar equality forces them onto `H`.
  refine ⟨hz i hit, ?_⟩
  simp [hboundary i hit hwi]

/-- Claim 5.4.1-extra-1. If every point of `A` lies in the closed halfspace
`gamma ⁻¹' Set.Iic gamma0`, then the points of `convexHull ℝ A` lying on the boundary hyperplane
`gamma ⁻¹' {gamma0}` are exactly the convex hull of the points of `A` already on that
hyperplane. -/
theorem convexHull_inter_hyperplane_eq
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : Set E)
    (gamma : E →ₗ[ℝ] ℝ)
    (gamma0 : ℝ)
    (hA : A ⊆ gamma ⁻¹' Set.Iic gamma0) :
    convexHull ℝ A ∩ gamma ⁻¹' {gamma0} =
      convexHull ℝ (A ∩ gamma ⁻¹' {gamma0}) := by
  classical
  letI : AddCommGroup E := Module.addCommMonoidToAddCommGroup ℝ
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rcases hx with ⟨hxHull, hxH⟩
    -- Rewrite the ambient convex-hull membership as a finite center-of-mass witness.
    rw [_root_.convexHull_eq] at hxHull ⊢
    rcases hxHull with ⟨ι, t, w, z, hw₀, hw₁, hz, hcenter⟩
    refine ⟨ι, {i ∈ t | w i ≠ 0}, w, z, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact hw₀ i (Finset.mem_filter.mp hi).1
    · -- Filtering away zero weights preserves the barycentric normalization.
      rw [Finset.sum_filter_ne_zero]
      exact hw₁
    · -- The textbook equality case shows every positive-weight support point lies on `H`.
      have hx_eq : gamma x = gamma0 := by
        simpa using hxH
      have hsum_eq : ∑ i ∈ t, w i • z i = x := by
        calc
          ∑ i ∈ t, w i • z i = t.centerMass w z := by
            rw [← t.centerMass_eq_of_sum_1 (w := w) (z := z) hw₁]
          _ = x := hcenter
      exact support_mem_hyperplane_of_centerMass_eq A gamma gamma0 hA t w z x hw₀ hw₁ hz hsum_eq
        hx_eq
    · -- Filtering away zero weights does not change the center of mass.
      calc
        {i ∈ t | w i ≠ 0}.centerMass w z = t.centerMass w z := by
          simpa using (Finset.centerMass_filter_ne_zero (t := t) (w := w) (z := z))
        _ = x := hcenter
  · -- The easy direction is the general convex-hull inclusion from the boundary subset.
    exact convexHull_subset_inter_hyperplane_of_subset A gamma gamma0
