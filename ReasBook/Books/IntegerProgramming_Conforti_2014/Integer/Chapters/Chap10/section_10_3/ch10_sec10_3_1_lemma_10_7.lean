import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_zero_one_points

open scoped Matrix

section Lemma107

variable {n : ℕ}

/-- The homogenized lift `(1, x)` of a vector `x ∈ ℝ^n`. -/
def homogenized_point (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons 1 x

/-- The conic hull used by the Lovasz-Schrijver lift, presented as nonnegative multiples of
homogenized points from `conv(P)`. -/
def homogenized_cone (P : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {y | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ convexHull ℝ P, y = t • homogenized_point x}

/-- Membership in `homogenized_cone P` unfolds to a nonnegative scalar multiple of a homogenized
point from `conv(P)`. -/
theorem mem_homogenized_cone_iff
    (P : Set (Fin n → ℝ))
    (y : Fin (n + 1) → ℝ) :
    y ∈ homogenized_cone P ↔
      ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ convexHull ℝ P, y = t • homogenized_point x :=
  Iff.rfl

/-- A point of `conv(P)` gives a homogenized point in `homogenized_cone P`. -/
theorem homogenized_point_mem_homogenized_cone
    (P : Set (Fin n → ℝ))
    {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ P) :
    homogenized_point x ∈ homogenized_cone P := by
  exact ⟨1, zero_le_one, x, hx, by simp⟩

/-- If the homogenized lift `(1, x)` lies in `homogenized_cone P`, then `x` lies in `conv(P)`. -/
theorem mem_convexHull_of_homogenized_point_mem_homogenized_cone
    (P : Set (Fin n → ℝ))
    {x : Fin n → ℝ}
    (hx : homogenized_point x ∈ homogenized_cone P) :
    x ∈ convexHull ℝ P := by
  rw [mem_homogenized_cone_iff] at hx
  rcases hx with ⟨t, ht, y, hy, hxy⟩
  have ht_one : t = 1 := by
    simpa [homogenized_point] using (congr_fun hxy 0).symm
  have hxy' : x = y := by
    funext i
    simpa [homogenized_point, ht_one] using congr_fun hxy i.succ
  exact hxy' ▸ hy

/-- The `i`th standard basis vector in the lifted space `ℝ^(n+1)`. -/
def lifted_basis (i : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  Pi.single i 1

/-- The lifted basis vector is `1` at its distinguished coordinate and `0` elsewhere. -/
theorem lifted_basis_apply
    (i j : Fin (n + 1)) :
    lifted_basis i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [lifted_basis]
  · simp [lifted_basis, h]

/-- The lifted basis vector is the canonical single-coordinate function `Pi.single i 1`. -/
theorem lifted_basis_eq_single
    (i : Fin (n + 1)) :
    lifted_basis i = Pi.single i 1 :=
  rfl

/-- Multiplying by `lifted_basis i` extracts the `i`th column of a lifted matrix. -/
theorem mulVec_lifted_basis
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) :
    Y *ᵥ lifted_basis i = fun j ↦ Y j i := by
  change Y *ᵥ Pi.single i 1 = Y.col i
  exact Matrix.mulVec_single_one Y i

/-- The matrix constraints defining the Lovasz-Schrijver lift before imposing positive
semidefiniteness. -/
def IsLovaszSchrijverMatrix
    (P : Set (Fin n → ℝ))
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  Yᵀ = Y ∧
    (Y *ᵥ lifted_basis 0) ∈ homogenized_cone P ∧
    (∀ i : Fin n,
      (Y *ᵥ lifted_basis i.succ) ∈ homogenized_cone P ∧
        (Y *ᵥ (lifted_basis 0 - lifted_basis i.succ)) ∈ homogenized_cone P) ∧
    ∀ i : Fin n, Y i.succ i.succ = Y i.succ 0

/-- Unfolding characterization of `IsLovaszSchrijverMatrix`. -/
theorem isLovaszSchrijverMatrix_iff
    (P : Set (Fin n → ℝ))
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    IsLovaszSchrijverMatrix P Y ↔
      Yᵀ = Y ∧
        (Y *ᵥ lifted_basis 0) ∈ homogenized_cone P ∧
        (∀ i : Fin n,
          (Y *ᵥ lifted_basis i.succ) ∈ homogenized_cone P ∧
            (Y *ᵥ (lifted_basis 0 - lifted_basis i.succ)) ∈ homogenized_cone P) ∧
        ∀ i : Fin n, Y i.succ i.succ = Y i.succ 0 :=
  Iff.rfl

/-- The linear Lovasz-Schrijver relaxation `N(P)`. -/
def lovasz_schrijver_N (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      IsLovaszSchrijverMatrix P Y ∧
        Y *ᵥ lifted_basis 0 = homogenized_point x}

/-- The semidefinite Lovasz-Schrijver relaxation `N₊(P)`. -/
def lovasz_schrijver_N_plus (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      IsLovaszSchrijverMatrix P Y ∧
        Y.PosSemidef ∧
        Y *ᵥ lifted_basis 0 = homogenized_point x}

namespace LovaszSchrijverNotation

scoped notation:max "N(" P ")" => lovasz_schrijver_N P
scoped notation:max "N₊(" P ")" => lovasz_schrijver_N_plus P

end LovaszSchrijverNotation

open scoped LovaszSchrijverNotation

/-- Membership in `N(P)` means admitting a lifted matrix with first column `(1, x)`. -/
theorem mem_lovasz_schrijver_N_iff
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ N(P) ↔
      ∃ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        IsLovaszSchrijverMatrix P Y ∧
          Y *ᵥ lifted_basis 0 = homogenized_point x :=
  Iff.rfl

/-- Membership in `N₊(P)` means admitting a positive-semidefinite lifted matrix with first column
`(1, x)`. -/
theorem mem_lovasz_schrijver_N_plus_iff
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ N₊(P) ↔
      ∃ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        IsLovaszSchrijverMatrix P Y ∧
          Y.PosSemidef ∧
          Y *ᵥ lifted_basis 0 = homogenized_point x :=
  Iff.rfl

/-- Helper for Lemma 10.7: nonnegative scaling preserves `homogenized_cone P`. -/
lemma homogenizedCone_nonneg_smul_mem
    (P : Set (Fin n → ℝ))
    {y : Fin (n + 1) → ℝ}
    {a : ℝ}
    (hy : y ∈ homogenized_cone P)
    (ha : 0 ≤ a) :
    a • y ∈ homogenized_cone P := by
  -- Unpack the cone witness and absorb the extra nonnegative factor into its scalar.
  rw [mem_homogenized_cone_iff] at hy ⊢
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  refine ⟨a * t, mul_nonneg ha ht, x, hx, ?_⟩
  simp [smul_smul]

/-- Helper for Lemma 10.7: `homogenized_cone P` is closed under addition. -/
lemma homogenizedCone_add_mem
    (P : Set (Fin n → ℝ))
    {y₁ y₂ : Fin (n + 1) → ℝ}
    (hy₁ : y₁ ∈ homogenized_cone P)
    (hy₂ : y₂ ∈ homogenized_cone P) :
    y₁ + y₂ ∈ homogenized_cone P := by
  -- Write both vectors with cone witnesses and normalize by the total scalar.
  rw [mem_homogenized_cone_iff] at hy₁ hy₂ ⊢
  rcases hy₁ with ⟨t₁, ht₁, x₁, hx₁, rfl⟩
  rcases hy₂ with ⟨t₂, ht₂, x₂, hx₂, rfl⟩
  by_cases hsum : t₁ + t₂ = 0
  · -- If the total scalar vanishes, both coefficients are zero and the sum is the zero cone point.
    have ht₁_zero : t₁ = 0 := by
      linarith
    have ht₂_zero : t₂ = 0 := by
      linarith
    refine ⟨0, le_rfl, x₁, hx₁, ?_⟩
    simp [ht₁_zero, ht₂_zero]
  · -- Otherwise the normalized coefficients define a convex combination in `conv(P)`.
    have hsum_nonneg : 0 ≤ t₁ + t₂ := add_nonneg ht₁ ht₂
    have hcoeff₁_nonneg : 0 ≤ t₁ / (t₁ + t₂) := by
      exact div_nonneg ht₁ hsum_nonneg
    have hcoeff₂_nonneg : 0 ≤ t₂ / (t₁ + t₂) := by
      exact div_nonneg ht₂ hsum_nonneg
    have hcoeff_sum : t₁ / (t₁ + t₂) + t₂ / (t₁ + t₂) = 1 := by
      field_simp [hsum]
    have hcombo_mem :
        (t₁ / (t₁ + t₂)) • x₁ + (t₂ / (t₁ + t₂)) • x₂ ∈ convexHull ℝ P := by
      exact (convex_convexHull ℝ P) hx₁ hx₂ hcoeff₁_nonneg hcoeff₂_nonneg hcoeff_sum
    refine ⟨t₁ + t₂, hsum_nonneg,
      (t₁ / (t₁ + t₂)) • x₁ + (t₂ / (t₁ + t₂)) • x₂, hcombo_mem, ?_⟩
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [homogenized_point]
    · intro j
      simp [homogenized_point]
      field_simp [hsum]

/-- Helper for Lemma 10.7: every binary feasible point has the standard rank-one witness in
`N₊(P)`. -/
lemma mem_lovaszSchrijverNPlus_of_mem_zeroOnePoints
    (P : Set (Fin n → ℝ))
    {x : Fin n → ℝ}
    (hx : x ∈ zero_one_points (Nat.le_refl n) P) :
    x ∈ N₊(P) := by
  -- Extract the point in `P` and its binary coordinates to build the rank-one witness.
  rw [mem_zero_one_points_iff (Nat.le_refl n) P x] at hx
  rcases hx with ⟨hxP, hx01raw⟩
  have hx01 : ∀ i : Fin n, x i = 0 ∨ x i = 1 := by
    simpa using hx01raw
  let u : Fin (n + 1) → ℝ := homogenized_point x
  let Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.vecMulVec u u
  have hxHull : x ∈ convexHull ℝ P := subset_convexHull ℝ P hxP
  have hcol0 : Y *ᵥ lifted_basis 0 = u := by
    -- The first column of the rank-one witness is the homogenized lift itself.
    ext j
    rw [mulVec_lifted_basis]
    simp [Y, u, Matrix.vecMulVec, homogenized_point]
  have hsymm : Yᵀ = Y := by
    -- A rank-one matrix `u uᵀ` is symmetric over `ℝ`.
    ext i j
    simp [Y, Matrix.vecMulVec, mul_comm]
  have hpsd : Y.PosSemidef := by
    -- Positive semidefiniteness is the standard `vecMulVec` fact.
    simpa [Y, u] using Matrix.posSemidef_vecMulVec_self_star u
  rw [mem_lovasz_schrijver_N_plus_iff]
  refine ⟨Y, ?_, hpsd, ?_⟩
  · -- The column constraints are exactly scalar multiples of the same homogenized point.
    rw [isLovaszSchrijverMatrix_iff]
    refine ⟨hsymm, ?_, ?_, ?_⟩
    · rw [hcol0]
      simpa [u] using homogenized_point_mem_homogenized_cone P hxHull
    · intro i
      have hxi_nonneg : 0 ≤ x i := by
        rcases hx01 i with hxi | hxi <;> linarith
      have hone_sub_nonneg : 0 ≤ 1 - x i := by
        rcases hx01 i with hxi | hxi <;> linarith
      have hxi_sq : x i * x i = x i := by
        rcases hx01 i with hxi | hxi
        · simp [hxi]
        · simp [hxi]
      have hcoli : Y *ᵥ lifted_basis i.succ = x i • u := by
        rw [mulVec_lifted_basis]
        ext j
        simp [Y, u, Matrix.vecMulVec, homogenized_point, mul_comm]
      have hcolDiff :
          Y *ᵥ (lifted_basis 0 - lifted_basis i.succ) = (1 - x i) • u := by
        rw [Matrix.mulVec_sub, hcol0, hcoli]
        ext j
        simp [one_sub_mul]
      refine ⟨?_, ?_⟩
      · rw [hcoli]
        exact homogenizedCone_nonneg_smul_mem P
          (homogenized_point_mem_homogenized_cone P hxHull) hxi_nonneg
      · rw [hcolDiff]
        exact homogenizedCone_nonneg_smul_mem P
          (homogenized_point_mem_homogenized_cone P hxHull) hone_sub_nonneg
    · intro i
      have hxi_sq : x i * x i = x i := by
        rcases hx01 i with hxi | hxi
        · simp [hxi]
        · simp [hxi]
      simp [Y, u, Matrix.vecMulVec, homogenized_point, hxi_sq]
  · simpa [u] using hcol0

/-- Helper for Lemma 10.7: the semidefinite Lovász-Schrijver lift is convex. -/
lemma convex_lovaszSchrijverNPlus
    (P : Set (Fin n → ℝ)) :
    Convex ℝ (N₊(P)) := by
  intro x hx y hy a b ha hb hab
  -- Convexly combine the two matrix witnesses and keep every constraint stable.
  rw [mem_lovasz_schrijver_N_plus_iff] at hx hy ⊢
  rcases hx with ⟨Yx, hYx, hYx_psd, hcolx⟩
  rcases hy with ⟨Yy, hYy, hYy_psd, hcoly⟩
  rw [isLovaszSchrijverMatrix_iff] at hYx hYy
  rcases hYx with ⟨hYx_symm, hYx0, hYxrest, hYxdiag⟩
  rcases hYy with ⟨hYy_symm, hYy0, hYyrest, hYydiag⟩
  refine ⟨a • Yx + b • Yy, ?_, ?_, ?_⟩
  · -- Symmetry, cone constraints, and diagonal constraints are preserved termwise.
    rw [isLovaszSchrijverMatrix_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        (a • Yx + b • Yy)ᵀ = a • Yxᵀ + b • Yyᵀ := by simp
        _ = a • Yx + b • Yy := by rw [hYx_symm, hYy_symm]
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYx0 ha)
        (homogenizedCone_nonneg_smul_mem P hYy0 hb)
    · intro i
      rcases hYxrest i with ⟨hYxi, hYxDiff⟩
      rcases hYyrest i with ⟨hYyi, hYyDiff⟩
      refine ⟨?_, ?_⟩
      · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
        exact homogenizedCone_add_mem P
          (homogenizedCone_nonneg_smul_mem P hYxi ha)
          (homogenizedCone_nonneg_smul_mem P hYyi hb)
      · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
        exact homogenizedCone_add_mem P
          (homogenizedCone_nonneg_smul_mem P hYxDiff ha)
          (homogenizedCone_nonneg_smul_mem P hYyDiff hb)
    · intro i
      simp [hYxdiag i, hYydiag i]
  · -- Positive semidefiniteness is stable under nonnegative scaling and addition.
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hYx_psd ha)
      (Matrix.PosSemidef.smul hYy_psd hb)
  · -- The first column becomes the homogenized lift of the convex combination.
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hcolx, hcoly]
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [homogenized_point, hab]
    · intro j
      simp [homogenized_point]

/-- Lemma 10.7 (1). The convex hull of the `0/1` feasible points of `P` is contained in the
Lovasz-Schrijver semidefinite relaxation `N₊(P)`. Here the source set
`S = P ∩ {0, 1}ⁿ` is formalized as `zero_one_points (Nat.le_refl n) P`. -/
theorem convexHull_zero_one_points_subset_lovasz_schrijver_N_plus
    (P : Set (Fin n → ℝ)) :
    convexHull ℝ (zero_one_points (Nat.le_refl n) P) ⊆ N₊(P) := by
  -- The hull stays inside `N₊(P)` because the binary points already lie there and
  -- `N₊(P)` is convex.
  refine convexHull_min ?_ (convex_lovaszSchrijverNPlus P)
  intro x hx
  exact mem_lovaszSchrijverNPlus_of_mem_zeroOnePoints P hx

/-- Lemma 10.7 (2). The semidefinite Lovasz-Schrijver relaxation is contained in the linear
Lovasz-Schrijver relaxation. -/
theorem lovasz_schrijver_N_plus_subset_N
    (P : Set (Fin n → ℝ)) :
    N₊(P) ⊆ N(P) := by
  intro x hx
  rw [mem_lovasz_schrijver_N_plus_iff] at hx
  rcases hx with ⟨Y, hY, -, hcol⟩
  exact (mem_lovasz_schrijver_N_iff P x).2 ⟨Y, hY, hcol⟩

/-- Lemma 10.7 (3). If the ambient relaxation `P` is convex, then the linear Lovasz-Schrijver
relaxation is contained in `P`. -/
theorem lovasz_schrijver_N_subset
    (P : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P) :
    N(P) ⊆ P := by
  intro x hx
  -- The first column witness already lies in the homogenized cone, so `x` lies in `conv(P) = P`.
  rw [mem_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol⟩
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨-, hY0, -, -⟩
  have hxHull : x ∈ convexHull ℝ P := by
    rw [hcol] at hY0
    exact mem_convexHull_of_homogenized_point_mem_homogenized_cone P hY0
  rwa [convexHull_eq_self.2 hP_convex] at hxHull

end Lemma107
