import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Pi

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped BigOperators Matrix Pointwise

section Claim1

variable {n : ℕ}

/-- An optimization oracle for `P ⊆ ℝ^n` returns, for each linear objective vector `c`, a point of
`P` maximizing `c · x` over all points of `P`. -/
def IsOptimizationOracle (P : Set (Fin n → ℝ)) (solve : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ c : Fin n → ℝ, solve c ∈ P ∧ ∀ y : Fin n → ℝ, y ∈ P → c ⬝ᵥ y ≤ c ⬝ᵥ solve c

/-- `IsOptimizationOracle P solve` unfolds to feasibility and linear-objective optimality of the
output `solve c` for every objective vector `c`. -/
theorem isOptimizationOracle_iff
    {P : Set (Fin n → ℝ)} {solve : (Fin n → ℝ) → (Fin n → ℝ)} :
    IsOptimizationOracle P solve ↔
      ∀ c : Fin n → ℝ, solve c ∈ P ∧ ∀ y : Fin n → ℝ, y ∈ P → c ⬝ᵥ y ≤ c ⬝ᵥ solve c := by
  rfl

namespace IsOptimizationOracle

variable {P : Set (Fin n → ℝ)} {solve : (Fin n → ℝ) → (Fin n → ℝ)}

/-- An optimization oracle returns a feasible point for every queried objective vector. -/
theorem mem (hsolve : IsOptimizationOracle P solve) (c : Fin n → ℝ) :
    solve c ∈ P :=
  (hsolve c).1

/-- The point returned by an optimization oracle maximizes the queried linear objective over `P`.
-/
theorem dotProduct_le
    (hsolve : IsOptimizationOracle P solve)
    (c : Fin n → ℝ)
    {y : Fin n → ℝ}
    (hy : y ∈ P) :
    c ⬝ᵥ y ≤ c ⬝ᵥ solve c :=
  (hsolve c).2 y hy

end IsOptimizationOracle

/-- For `n + 1` equally weighted points of `ℝ^n`, `Finset.univ.centerMass` is their arithmetic
mean. -/
theorem univ_centerMass_eq_arithmeticMean (x : Fin (n + 1) → (Fin n → ℝ)) :
    Finset.univ.centerMass (fun _ : Fin (n + 1) ↦ (1 : ℝ)) x =
      ((n + 1 : ℝ)⁻¹) • ∑ i : Fin (n + 1), x i := by
  simp [Finset.centerMass]

/-- Helper for Claim 1: every linear functional on `Fin n → ℝ` is the dot product with a
coefficient vector. -/
lemma exists_eq_dotProductBilin (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    ∃ c : Fin n → ℝ, f = dotProductBilin ℝ ℝ c := by
  classical
  let c : Fin n → ℝ := fun i => f (Pi.single i 1)
  -- Compare the linear maps on the standard basis vectors of the finite product space.
  refine ⟨c, ?_⟩
  apply LinearMap.pi_ext
  intro i x
  have hsingle : Pi.single i x = x • Pi.single i (1 : ℝ) := by
    ext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  rw [hsingle, map_smul]
  simp [c, mul_comm]

/-- Helper for Claim 1: a set contained in one nontrivial dot-product level set cannot have full
affine span. -/
lemma affineSpan_ne_top_of_forall_dotProduct_eq
    {P : Set (Fin n → ℝ)} {c x0 : Fin n → ℝ}
    (hc : c ≠ 0)
    (hconst : ∀ y ∈ P, c ⬝ᵥ y = c ⬝ᵥ x0) :
    affineSpan ℝ P ≠ ⊤ := by
  let H : AffineSubspace ℝ (Fin n → ℝ) :=
    AffineSubspace.mk' x0 (LinearMap.ker (dotProductBilin ℝ ℝ c))
  have hP_le : P ⊆ H := by
    intro y hy
    -- Rewrite membership in the affine hyperplane as a vanishing dot-product difference.
    change y ∈ H
    rw [AffineSubspace.mem_mk']
    change c ⬝ᵥ (y - x0) = 0
    rw [dotProduct_sub]
    linarith [hconst y hy]
  intro htop
  have hH_top : H = ⊤ := by
    -- If `P` spans all of `ℝ^n`, then the containing hyperplane would have to be all of `ℝ^n`.
    apply top_unique
    simpa [htop] using (affineSpan_le (Q := H)).2 hP_le
  have hx_mem : x0 + c ∈ H := by
    simp [hH_top]
  have hx_not_mem : x0 + c ∉ H := by
    -- The direction kernel is proper because `c` is nonzero.
    rw [AffineSubspace.mem_mk']
    change c ⬝ᵥ ((x0 + c) - x0) ≠ 0
    simp [hc]
  exact hx_not_mem hx_mem

/-- Helper for Claim 1: the image of an exact optimization oracle already has full affine span. -/
lemma oracleRange_affineSpan_eq_top
    {P : Set (Fin n → ℝ)}
    (hP_full_dimensional : affineSpan ℝ P = ⊤)
    (solve : (Fin n → ℝ) → (Fin n → ℝ))
    (hsolve : IsOptimizationOracle P solve) :
    affineSpan ℝ (Set.range solve) = ⊤ := by
  classical
  let A : AffineSubspace ℝ (Fin n → ℝ) := affineSpan ℝ (Set.range solve)
  let x0 : Fin n → ℝ := solve 0
  have hx0_mem_A : x0 ∈ A := by
    exact mem_affineSpan ℝ (Set.mem_range_self 0)
  have hA_nonempty : (A : Set (Fin n → ℝ)).Nonempty := ⟨x0, hx0_mem_A⟩
  by_contra hA_top
  have hA_dir_ne_top : A.direction ≠ ⊤ := by
    intro hdir_top
    exact hA_top ((AffineSubspace.direction_eq_top_iff_of_nonempty hA_nonempty).1 hdir_top)
  have hA_dir_lt_top : A.direction < ⊤ := lt_of_le_of_ne le_top hA_dir_ne_top
  -- Separate the proper direction subspace by a nonzero linear functional.
  obtain ⟨f, hf_nonzero, hdir_le_ker⟩ := A.direction.exists_le_ker_of_lt_top hA_dir_lt_top
  obtain ⟨c, hc_eq⟩ := exists_eq_dotProductBilin f
  have hc_nonzero : c ≠ 0 := by
    intro hc_zero
    apply hf_nonzero
    ext y
    simp [hc_eq, hc_zero]
  have hconst_range : ∀ z ∈ Set.range solve, c ⬝ᵥ z = c ⬝ᵥ x0 := by
    intro z hz
    have hz_mem_A : z ∈ A := mem_affineSpan ℝ hz
    have hz_vsub : z - x0 ∈ A.direction := A.vsub_mem_direction hz_mem_A hx0_mem_A
    have hker : f (z - x0) = 0 := hdir_le_ker hz_vsub
    -- Points in the oracle range differ from `x0` by vectors annihilated by `f`.
    have hdot : c ⬝ᵥ (z - x0) = 0 := by
      simpa [hc_eq] using hker
    rw [dotProduct_sub] at hdot
    linarith
  have hconst_P : ∀ y ∈ P, c ⬝ᵥ y = c ⬝ᵥ x0 := by
    intro y hy
    -- Optimality for `c` gives the upper bound, and optimality for `-c` gives the lower bound.
    have hupper_oracle : c ⬝ᵥ y ≤ c ⬝ᵥ solve c := hsolve.dotProduct_le c hy
    have hupper_value : c ⬝ᵥ solve c = c ⬝ᵥ x0 := hconst_range (solve c) (Set.mem_range_self c)
    have hupper : c ⬝ᵥ y ≤ c ⬝ᵥ x0 := by
      linarith
    have hlower_oracle : (-c) ⬝ᵥ y ≤ (-c) ⬝ᵥ solve (-c) := hsolve.dotProduct_le (-c) hy
    have hlower_value : (-c) ⬝ᵥ solve (-c) = (-c) ⬝ᵥ x0 := by
      have hneg := hconst_range (solve (-c)) (Set.mem_range_self (-c))
      simpa using congrArg Neg.neg hneg
    have hlower_neg : -(c ⬝ᵥ y) ≤ -(c ⬝ᵥ x0) := by
      calc
        -(c ⬝ᵥ y) = (-c) ⬝ᵥ y := by simp
        _ ≤ (-c) ⬝ᵥ solve (-c) := hlower_oracle
        _ = -(c ⬝ᵥ x0) := by simpa using hlower_value
    have hlower : c ⬝ᵥ x0 ≤ c ⬝ᵥ y := by
      linarith
    linarith
  exact (affineSpan_ne_top_of_forall_dotProduct_eq hc_nonzero hconst_P) hP_full_dimensional

/-- Helper for Claim 1: a full-dimensional oracle range contains an affine basis indexed by
`Fin (n + 1)`. -/
lemma exists_affineBasis_of_oracleRange
    (solve : (Fin n → ℝ) → (Fin n → ℝ))
    (hspan : affineSpan ℝ (Set.range solve) = ⊤) :
    ∃ b : AffineBasis (Fin (n + 1)) ℝ (Fin n → ℝ), Set.range b ⊆ Set.range solve := by
  classical
  obtain ⟨s, hs, b, hb⟩ := AffineBasis.exists_affine_subbasis hspan
  have hsubset : Set.range b ⊆ Set.range solve := by
    simpa [hb] using hs
  letI : Fintype s := b.finite_set.fintype
  have hcard : Fintype.card s = n + 1 := by
    -- The affine basis has exactly `finrank + 1` points, and `finrank ℝ (Fin n → ℝ) = n`.
    rw [b.card_eq_finrank_add_one, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hcard' : Fintype.card s = Fintype.card (Fin (n + 1)) := by
    simpa using hcard
  let e : s ≃ Fin (n + 1) := Fintype.equivOfCardEq hcard'
  refine ⟨b.reindex e, ?_⟩
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact hsubset ⟨e.symm i, rfl⟩

/-- Claim 1. If Optimization can be solved in polynomial time on `P`, then an interior point of
`P` can be found in polynomial time. On the exact oracle surface used here, if `P ⊆ ℝ^n` is
convex and full-dimensional and `solve` returns an optimizer for each linear objective, then there
are `n + 1` objective vectors whose optimizer outputs are affinely independent and whose arithmetic
mean, equivalently equally weighted center of mass, lies in `interior P`. -/
theorem optimization_oracle_yields_interior_barycenter
    {P : Set (Fin n → ℝ)}
    (hP_convex : Convex ℝ P)
    (hP_full_dimensional : affineSpan ℝ P = ⊤)
    (solve : (Fin n → ℝ) → (Fin n → ℝ))
    (hsolve : IsOptimizationOracle P solve) :
    ∃ objectives : Fin (n + 1) → (Fin n → ℝ),
      AffineIndependent ℝ (solve ∘ objectives) ∧
        (∀ i : Fin (n + 1), solve (objectives i) ∈ P) ∧
        ((n + 1 : ℝ)⁻¹) • ∑ i : Fin (n + 1), solve (objectives i) ∈ interior P := by
  classical
  -- Route correction: instead of recreating the source's iterative construction, use that the
  -- oracle image already spans affinely, then extract an affine basis from that image.
  have horacle_span : affineSpan ℝ (Set.range solve) = ⊤ :=
    oracleRange_affineSpan_eq_top hP_full_dimensional solve hsolve
  obtain ⟨b, hb_range⟩ := exists_affineBasis_of_oracleRange solve horacle_span
  have hpreimages : ∀ i : Fin (n + 1), ∃ objective, solve objective = b i := by
    intro i
    exact hb_range ⟨i, rfl⟩
  choose objectives hobjective using hpreimages
  have hfamily : solve ∘ objectives = b := by
    funext i
    exact hobjective i
  have hAffineIndependent : AffineIndependent ℝ (solve ∘ objectives) := by
    -- The oracle outputs inherit affine independence from the extracted affine basis.
    simpa [hfamily] using b.ind
  have hFeasible : ∀ i : Fin (n + 1), solve (objectives i) ∈ P := by
    intro i
    exact hsolve.mem (objectives i)
  have hrange_subset : Set.range b ⊆ P := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    simpa [hobjective i] using hFeasible i
  have hconvexHull_subset : convexHull ℝ (Set.range b) ⊆ P := convexHull_min hrange_subset hP_convex
  have hcentroid_conv : Finset.univ.centroid ℝ b ∈ interior (convexHull ℝ (Set.range b)) := by
    -- The centroid of an affine basis lies in the interior of its convex hull.
    simpa using b.centroid_mem_interior_convexHull
  have hcentroid_mem : Finset.univ.centroid ℝ b ∈ interior P := by
    exact interior_mono hconvexHull_subset hcentroid_conv
  have hcentroid_objectives : Finset.univ.centroid ℝ (solve ∘ objectives) ∈ interior P := by
    simpa only [hfamily] using hcentroid_mem
  have hMean : ((n + 1 : ℝ)⁻¹) • ∑ i : Fin (n + 1), solve (objectives i) ∈ interior P := by
    -- Unfold the centroid weights on `Finset.univ` and then normalize the common scalar factor.
    have hcenterMass :
        (((n + 1 : ℝ) * (n + 1 : ℝ)⁻¹) •
            ∑ x : Fin (n + 1), (n + 1 : ℝ)⁻¹ • solve (objectives x)) ∈ interior P := by
      simpa [Finset.centerMass, Finset.centroidWeights_eq_const, Function.comp_apply,
        Fintype.card_fin] using hcentroid_objectives
    have hcenterMass_eq :
        (((n + 1 : ℝ) * (n + 1 : ℝ)⁻¹) •
            ∑ x : Fin (n + 1), (n + 1 : ℝ)⁻¹ • solve (objectives x)) =
          ((n + 1 : ℝ)⁻¹) • ∑ x : Fin (n + 1), solve (objectives x) := by
      have hne : (n + 1 : ℝ) ≠ 0 := by
        positivity
      calc
        (((n + 1 : ℝ) * (n + 1 : ℝ)⁻¹) •
            ∑ x : Fin (n + 1), (n + 1 : ℝ)⁻¹ • solve (objectives x))
            = (1 : ℝ) • ∑ x : Fin (n + 1), (n + 1 : ℝ)⁻¹ • solve (objectives x) := by
              rw [mul_inv_cancel₀ hne]
        _ = ∑ x : Fin (n + 1), (n + 1 : ℝ)⁻¹ • solve (objectives x) := by
              simp
        _ = ((n + 1 : ℝ)⁻¹) • ∑ x : Fin (n + 1), solve (objectives x) := by
              rw [Finset.smul_sum]
    exact hcenterMass_eq ▸ hcenterMass
  exact ⟨objectives, hAffineIndependent, hFeasible, hMean⟩

/-- Translating `P` by `-xbar` moves the origin into the interior of the translated set
`(-xbar) +ᵥ P`. -/
theorem zero_mem_interior_neg_vadd_of_mem_interior
    {P : Set (Fin n → ℝ)} {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ interior P) :
    (0 : Fin n → ℝ) ∈ interior ((-xbar) +ᵥ P) := by
  rw [interior_vadd, Set.mem_vadd_set]
  exact ⟨xbar, hxbar, by simp [vadd_eq_add]⟩

end Claim1
