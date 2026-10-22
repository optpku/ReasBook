/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

section

variable {m n : ℕ}

/-- The transpose image of the nonnegative orthant in `ℝᵐ`, realized as the image of the positive
cone under `Aᵀ.mulVecLin`. -/
noncomputable abbrev transpose_nonnegative_cone (A : Matrix (Fin m) (Fin n) ℝ) :
    PointedCone ℝ (Fin n → ℝ) :=
  (PointedCone.positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin

@[simp] theorem mem_transpose_nonnegative_cone
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    c ∈ transpose_nonnegative_cone A ↔
      ∃ y ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ y = c := by
  constructor
  · intro hc
    change c ∈ ((PointedCone.positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin :
        PointedCone ℝ (Fin n → ℝ)) at hc
    rcases (PointedCone.mem_map).mp hc with ⟨y, hy, hyc⟩
    refine ⟨y, ?_, ?_⟩
    · simpa [PointedCone.mem_positive] using hy
    have hyc' : y ᵥ* A = c := by
      simpa [Matrix.mulVecLin_apply] using hyc
    exact (Matrix.mulVec_transpose A y).trans hyc'
  · rintro ⟨y, hy, hyc⟩
    change c ∈ ((PointedCone.positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin :
        PointedCone ℝ (Fin n → ℝ))
    refine (PointedCone.mem_map).2 ⟨y, ?_, ?_⟩
    · simpa [PointedCone.mem_positive] using hy
    have hyc' : y ᵥ* A = c := (Matrix.mulVec_transpose A y).symm.trans hyc
    simpa [Matrix.mulVecLin_apply] using hyc'

/- The standard bilinear pairing on `Fin n → ℝ` is the coordinate `dotProduct`. -/
private noncomputable abbrev dotProductPairing (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  dotProductBilin ℝ ℝ

/- The vectors `x` satisfying `A *ᵥ x ≤ 0` are exactly the dual cone of the negative transpose
image of the nonnegative orthant. -/
private theorem mem_dual_negativeTransposeImage_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ PointedCone.dual (dotProductPairing n)
        ((((PointedCone.positive ℝ (Fin m → ℝ)).map (-Aᵀ).mulVecLin :
            PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) ↔
      A *ᵥ x ≤ (0 : Fin m → ℝ) := by
  constructor
  · intro hx i
    -- Test the dual inequality on the image of the `i`th coordinate basis vector.
    have hmem :
        (-A).row i ∈
          (PointedCone.positive ℝ (Fin m → ℝ)).map (-Aᵀ).mulVecLin := by
      rw [PointedCone.mem_map]
      refine ⟨Pi.single i 1, ?_, ?_⟩
      · simp [PointedCone.mem_positive]
      · ext j
        simp
    have h := hx hmem
    -- Rewrite the tested generator into the corresponding coordinate of `A *ᵥ x`.
    simpa [dotProductPairing, Matrix.mulVec, dotProduct, neg_dotProduct] using h
  · intro hx z hz
    -- Pull a point of the image cone back to a nonnegative multiplier `y`.
    rcases (PointedCone.mem_map).mp hz with ⟨y, hy, rfl⟩
    have hy' : (0 : Fin m → ℝ) ≤ y := by
      simpa [PointedCone.mem_positive] using hy
    have hAy : 0 ≤ dotProduct y (-(A *ᵥ x)) := by
      refine dotProduct_nonneg_of_nonneg hy' ?_
      simpa using fun i ↦ neg_nonneg.mpr (hx i)
    -- Rewrite the dual pairing through the transpose matrix identity.
    simpa [dotProductPairing, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose, dotProduct_neg] using hAy

/- Membership of `-c` in the negative transpose image is equivalent to a nonnegative multiplier
`y` satisfying `Aᵀ *ᵥ y = c`. -/
private theorem neg_mem_negativeTransposeImage_iff
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    -c ∈ (PointedCone.positive ℝ (Fin m → ℝ)).map (-Aᵀ).mulVecLin ↔
      ∃ y ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ y = c := by
  constructor
  · intro hc
    rcases (PointedCone.mem_map).mp hc with ⟨y, hy, hAy⟩
    refine ⟨y, ?_, ?_⟩
    · simpa [PointedCone.mem_positive] using hy
    -- Cancel the global minus sign to recover the certificate equation.
    have hneg : -(Aᵀ *ᵥ y) = -c := by
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] using hAy
    exact neg_injective hneg
  · rintro ⟨y, hy, hAy⟩
    rw [PointedCone.mem_map]
    refine ⟨y, ?_, ?_⟩
    · simpa [PointedCone.mem_positive] using hy
    -- Reinsert the global minus sign so the witness lands in the negative image cone.
    have hneg : -(Aᵀ *ᵥ y) = -c := congrArg Neg.neg hAy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] using hneg

/- Mapping the positive orthant by a linear map is the ordinary image of `Set.Ici 0`. -/
private theorem positiveMap_eq_imageIci
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ((((PointedCone.positive ℝ (Fin m → ℝ)).map f : PointedCone ℝ (Fin n → ℝ)) :
      Set (Fin n → ℝ))) =
      f '' Set.Ici (0 : Fin m → ℝ) := by
  ext z
  constructor
  · intro hz
    -- Unpack cone-image membership into a nonnegative source witness.
    rcases (PointedCone.mem_map).mp hz with ⟨y, hy, rfl⟩
    exact ⟨y, by simpa [PointedCone.mem_positive] using hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    -- Repackage an ordinary nonnegative witness as pointed-cone membership.
    exact (PointedCone.mem_map).2 ⟨y, by simpa [PointedCone.mem_positive] using hy, rfl⟩

/- Every point of `f '' Set.Ici 0` has a nonnegative preimage of minimal norm. -/
private theorem existsMinNormNonnegativePreimage
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) {z : Fin n → ℝ}
    (hz : z ∈ f '' Set.Ici (0 : Fin m → ℝ)) :
    ∃ y ∈ Set.Ici (0 : Fin m → ℝ), f y = z ∧
      ∀ y' ∈ Set.Ici (0 : Fin m → ℝ), f y' = z → ‖y‖ ≤ ‖y'‖ := by
  rcases hz with ⟨y₀, hy₀, rfl⟩
  let K : Set (Fin m → ℝ) :=
    Set.Ici (0 : Fin m → ℝ) ∩ (f ⁻¹' {f y₀} ∩ Metric.closedBall 0 ‖y₀‖)
  have hfcont : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hKclosed : IsClosed K := by
    -- The feasible set is an intersection of closed constraints and a compact closed ball.
    refine isClosed_Ici.inter ?_
    refine (isClosed_singleton.preimage hfcont).inter Metric.isClosed_closedBall
  have hKcompact : IsCompact K := by
    refine (isCompact_closedBall (0 : Fin m → ℝ) ‖y₀‖).of_isClosed_subset hKclosed ?_
    intro y hy
    exact hy.2.2
  have hKnonempty : K.Nonempty := by
    refine ⟨y₀, hy₀, ?_⟩
    refine ⟨by simp, ?_⟩
    simp [Metric.mem_closedBall, dist_eq_norm]
  obtain ⟨y, hyK, hyMin⟩ :=
    hKcompact.exists_isMinOn hKnonempty continuous_norm.continuousOn
  refine ⟨y, hyK.1, hyK.2.1, ?_⟩
  intro y' hy' hy'_map
  have hy_le_y₀ : ‖y‖ ≤ ‖y₀‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hyK.2.2
  by_cases hy'ball : ‖y'‖ ≤ ‖y₀‖
  · -- Inside the compact feasible slice, minimality is built into `hyMin`.
    exact hyMin ⟨hy', by simp [hy'_map], by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy'ball⟩
  · -- Outside the controlling ball, the minimizer is automatically no larger.
    exact le_trans hy_le_y₀ (le_of_not_ge hy'ball)

/- Helper for Lemma 2.5: express a vector through the standard basis of `Fin m → ℝ`. -/
private theorem linearMap_apply_eq_sum_single
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ) :
    f x = Finset.univ.sum (fun i ↦ x i • f (fun j ↦ if i = j then 1 else 0)) := by
  -- Use the canonical basis expansion already available for Pi spaces.
  simpa using LinearMap.pi_apply_eq_sum_univ f x

/-- Helper for Lemma 2.5: the cone slice indexed by a finite support is the image of the
nonnegative orthant on that support under the corresponding coefficient map. -/
private noncomputable def coneSliceLinMap
    (v : Fin m → Fin n → ℝ) (s : Finset (Fin m)) :
    (s → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun a := ∑ i : s, a i • v i
  map_add' a b := by
    -- Sum coefficientwise to expose linearity on the finite support.
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    -- Pull the scalar through the finite sum.
    simp [smul_smul, Finset.smul_sum]

/-- Helper for Lemma 2.5: the set of conical combinations supported on `s`. -/
private noncomputable def coneSlice
    (v : Fin m → Fin n → ℝ) (s : Finset (Fin m)) : Set (Fin n → ℝ) :=
  coneSliceLinMap v s '' Set.Ici (0 : s → ℝ)

/-- Helper for Lemma 2.5: a simplicial cone slice is closed because its coefficient map is an
injective finite-dimensional linear embedding. -/
private theorem coneSlice_isClosed
    (v : Fin m → Fin n → ℝ) (s : Finset (Fin m))
    (hs_lin : LinearIndepOn ℝ v (s : Set (Fin m))) :
    IsClosed (coneSlice v s) := by
  let L := coneSliceLinMap v s
  have hLin : LinearIndependent ℝ (fun i : s ↦ v i) := by
    simpa [LinearIndepOn] using hs_lin
  have hker : L.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a hzero
    rw [Fintype.linearIndependent_iff] at hLin
    ext i
    exact hLin a (by simpa [coneSliceLinMap, L] using hzero) i
  have hClosedEmbedding : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective hker
  -- Push closedness of the orthant through the closed embedding.
  simpa [coneSlice, L] using hClosedEmbedding.isClosedMap _ isClosed_Ici

/-- Helper for Lemma 2.5: a dependent finite family admits a vanishing relation with at least one
strictly positive coefficient after a possible global sign flip. -/
private theorem existsDependenceWithPositiveCoefficient
    (v : Fin m → Fin n → ℝ) (s : Finset (Fin m))
    (hs_dep : ¬ LinearIndepOn ℝ v (s : Set (Fin m))) :
    ∃ d : Fin m → ℝ, s.sum (fun i ↦ d i • v i) = 0 ∧ ∃ i ∈ s, 0 < d i := by
  rcases (not_linearIndepOn_finset_iff).mp hs_dep with ⟨d, hd_sum, i, hi, hdi_ne⟩
  by_cases hdi_pos : 0 < d i
  · -- The initial dependence already points in a positive direction.
    exact ⟨d, hd_sum, i, hi, hdi_pos⟩
  · -- Otherwise negate the relation so that the chosen nonzero coefficient becomes positive.
    refine ⟨fun j ↦ -d j, ?_, i, hi, ?_⟩
    · simpa [neg_smul] using congrArg Neg.neg hd_sum
    · have hdi_neg : d i < 0 := lt_of_le_of_ne (le_of_not_gt hdi_pos) hdi_ne
      simpa using neg_pos.mpr hdi_neg

/-- Helper for Lemma 2.5: a nonnegative coefficient sum may be restricted to the actual positive
support without changing its value. -/
private theorem sum_filter_pos_eq
    (v : Fin m → Fin n → ℝ) (s : Finset (Fin m)) (a : Fin m → ℝ)
    (ha_nonneg : ∀ i ∈ s, 0 ≤ a i) :
    (s.filter (fun i ↦ 0 < a i)).sum (fun i ↦ a i • v i) = s.sum (fun i ↦ a i • v i) := by
  -- Terms outside the positive support vanish because nonnegativity forces them to be zero.
  symm
  rw [Finset.sum_filter_of_ne]
  intro i hi hi_term
  have hai_ne : a i ≠ 0 := by
    intro hai
    apply hi_term
    simp [hai]
  exact lt_of_le_of_ne (ha_nonneg i hi) (by simpa [eq_comm] using hai_ne)

/-- Helper for Lemma 2.5: applying a linear map to a nonnegative vector expands as a conical sum
over its actual positive support. -/
private theorem linearMap_apply_eq_sum_positiveSupport
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (y : Fin m → ℝ)
    (hy : y ∈ Set.Ici (0 : Fin m → ℝ)) :
    f y =
      (Finset.univ.filter (fun i ↦ 0 < y i)).sum
        (fun i ↦ y i • f (fun j ↦ if i = j then 1 else 0)) := by
  -- First expand in the standard basis, then discard the zero coefficients.
  have hy_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ y i := by
    intro i _
    exact hy i
  rw [linearMap_apply_eq_sum_single]
  symm
  exact sum_filter_pos_eq (fun i ↦ f (fun j ↦ if i = j then 1 else 0)) Finset.univ y hy_nonneg

/- Helper for Lemma 2.5: once a nonnegative sequence converges coordinatewise, subtracting half of
the nonnegative limit still stays inside the orthant eventually. -/
private theorem eventually_sub_half_limit_mem_Ici
    {u : Fin m → ℝ} {v : ℕ → Fin m → ℝ}
    (hv : Filter.Tendsto v Filter.atTop (nhds u))
    (hu : u ∈ Set.Ici (0 : Fin m → ℝ))
    (hv_nonneg : ∀ k, v k ∈ Set.Ici (0 : Fin m → ℝ)) :
    ∀ᶠ k in Filter.atTop, v k - (1 / 2 : ℝ) • u ∈ Set.Ici (0 : Fin m → ℝ) := by
  rw [tendsto_pi_nhds] at hv
  have hcoord :
      ∀ i : Fin m, ∀ᶠ k in Filter.atTop, 0 ≤ v k i - (1 / 2 : ℝ) * u i := by
    intro i
    by_cases hui : u i = 0
    · -- When the limit coordinate vanishes, the original orthant constraint is enough.
      filter_upwards [Filter.Eventually.of_forall fun k => hv_nonneg k i] with k hk
      simpa [hui]
    · have hui_pos : 0 < u i := lt_of_le_of_ne (hu i) (by simpa [eq_comm] using hui)
      have hball :
          Metric.ball (u i) (u i / 2) ∈ nhds (u i) := Metric.ball_mem_nhds _ (by positivity)
      have hv_half : ∀ᶠ k in Filter.atTop, v k i ∈ Metric.ball (u i) (u i / 2) := (hv i) hball
      -- Eventually each coordinate lies within half its limiting value, so it stays above half.
      filter_upwards [hv_half] with k hk
      have hk' : |v k i - u i| < u i / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hk
      have hk_left : -(u i / 2) < v k i - u i := (abs_lt.mp hk').1
      have hhalf : u i / 2 ≤ v k i := by
        linarith
      linarith
  have hfinite :
      ∀ s : Finset (Fin m), ∀ᶠ k in Filter.atTop, ∀ i ∈ s, 0 ≤ v k i - (1 / 2 : ℝ) * u i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact Filter.Eventually.of_forall (by simp)
    · intro a s ha hs
      filter_upwards [hcoord a, hs] with k hka hks i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact hka
      · exact hks i hi'
  -- Reassemble the coordinatewise inequalities into eventual membership of the orthant.
  filter_upwards [hfinite Finset.univ] with k hk
  exact fun i => by
    simpa [Pi.sub_apply] using hk i (by simp)

/-- Helper for Lemma 2.5: an unbounded sequence has a strictly increasing subsequence with
arbitrarily large norm. -/
private theorem existsLargeNormSubsequence_of_not_bounded
    {ySeq : ℕ → Fin m → ℝ}
    (hy_unbounded : ¬ Bornology.IsBounded (Set.range ySeq)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ ‖ySeq (φ k)‖ := by
  classical
  have hlargeTail : ∀ N : ℕ, ∀ R : ℝ, ∃ n ≥ N, R < ‖ySeq n‖ := by
    intro N R
    by_contra hNR
    apply hy_unbounded
    let B : ℝ := max R (Finset.sum (Finset.range N) fun i ↦ ‖ySeq i‖)
    refine (isBounded_iff_forall_norm_le (E := Fin m → ℝ) (s := Set.range ySeq)).2 ?_
    refine ⟨B, ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n < N
    · -- Early indices are controlled by the finite initial sum.
      have hmem : n ∈ Finset.range N := by simpa using hn
      have hsum :
          ‖ySeq n‖ ≤ Finset.sum (Finset.range N) (fun i ↦ ‖ySeq i‖) := by
        exact Finset.single_le_sum (fun i _ ↦ norm_nonneg _) hmem
      exact hsum.trans (le_max_right _ _)
    · -- After the cutoff, the negated existence claim bounds every remaining norm by `R`.
      have htail : ‖ySeq n‖ ≤ R := by
        by_contra hR
        exact hNR ⟨n, Nat.le_of_not_lt hn, lt_of_not_ge hR⟩
      exact htail.trans (le_max_left _ _)
  let φ : ℕ → ℕ :=
    Nat.rec (Classical.choose (hlargeTail 0 1))
      (fun k prev => Classical.choose (hlargeTail (prev + 1) ((k : ℝ) + 2)))
  have hφ_step :
      ∀ k, φ k < φ (k + 1) := by
    intro k
    have hk : φ k + 1 ≤ φ (k + 1) := by
      change φ k + 1 ≤ Classical.choose (hlargeTail (φ k + 1) ((k : ℝ) + 2))
      exact (Classical.choose_spec (hlargeTail (φ k + 1) ((k : ℝ) + 2))).1
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hk
  have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ hφ_step
  refine ⟨φ, hφ_mono, ?_⟩
  intro k
  cases k with
  | zero =>
      simpa [φ] using le_of_lt (Classical.choose_spec (hlargeTail 0 1)).2
  | succ k =>
      have hk :
          (k : ℝ) + 2 ≤ ‖ySeq (φ (k + 1))‖ := by
        simpa [φ] using
          le_of_lt (Classical.choose_spec (hlargeTail (φ k + 1) ((k : ℝ) + 2))).2
      convert hk using 1
      have hEq : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
      simpa [Nat.cast_add] using hEq

/-- Helper for Lemma 2.5: a normalized large-norm subsequence has a convergent further subsequence
whose limit is a nonnegative unit vector in the kernel of `f`. -/
private theorem existsNormalizedKernelLimit_of_largeNormSubsequence
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    {z : Fin n → ℝ} {zSeq : ℕ → Fin n → ℝ} {ySeq : ℕ → Fin m → ℝ}
    (hzSeq : Filter.Tendsto zSeq Filter.atTop (nhds z))
    (hySeq_nonneg : ∀ k, ySeq k ∈ Set.Ici (0 : Fin m → ℝ))
    (hySeq_map : ∀ k, f (ySeq k) = zSeq k)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hφ_large : ∀ k : ℕ, (k : ℝ) + 1 ≤ ‖ySeq (φ k)‖) :
    ∃ u : Fin m → ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (fun k ↦ ‖ySeq (φ (ψ k))‖⁻¹ • ySeq (φ (ψ k))) Filter.atTop (nhds u) ∧
      u ∈ Set.Ici (0 : Fin m → ℝ) ∧ f u = 0 ∧ ‖u‖ = 1 := by
  let uSeq : ℕ → Fin m → ℝ := fun k ↦ ‖ySeq (φ k)‖⁻¹ • ySeq (φ k)
  have huSeq_nonneg : ∀ k, uSeq k ∈ Set.Ici (0 : Fin m → ℝ) := by
    intro k i
    -- Normalization preserves coordinatewise nonnegativity because the scale is nonnegative.
    simpa [uSeq, Pi.smul_apply] using
      mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (hySeq_nonneg (φ k) i)
  have huSeq_norm : ∀ k, ‖uSeq k‖ = 1 := by
    intro k
    have hpos : 0 < ‖ySeq (φ k)‖ := by
      have hk : 0 < (k : ℝ) + 1 := by positivity
      exact lt_of_lt_of_le hk (hφ_large k)
    -- The chosen lower bound keeps the normalization denominator away from zero.
    calc
      ‖uSeq k‖ = |‖ySeq (φ k)‖⁻¹| * ‖ySeq (φ k)‖ := by
        dsimp [uSeq]
        rw [norm_smul, Real.norm_eq_abs]
      _ = ‖ySeq (φ k)‖⁻¹ * ‖ySeq (φ k)‖ := by
        rw [abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have huSeq_ball : ∀ k, uSeq k ∈ Metric.closedBall 0 1 := by
    intro k
    -- Unit-norm normalization places the sequence in a compact closed ball.
    simp [Metric.mem_closedBall, dist_eq_norm, huSeq_norm k]
  obtain ⟨u, hu_ball, ψ, hψ, hψ_tendsto⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : Fin m → ℝ) 1) huSeq_ball
  have hu_nonneg : u ∈ Set.Ici (0 : Fin m → ℝ) := by
    -- Closedness of the orthant passes nonnegativity to the subsequential limit.
    apply isClosed_Ici.mem_of_tendsto hψ_tendsto
    exact Filter.Eventually.of_forall fun k ↦ huSeq_nonneg (ψ k)
  have hu_norm : ‖u‖ = 1 := by
    have hnorm_tendsto :
        Filter.Tendsto (fun k ↦ ‖uSeq (ψ k)‖) Filter.atTop (nhds ‖u‖) :=
      continuous_norm.continuousAt.tendsto.comp hψ_tendsto
    have hconst_tendsto :
        Filter.Tendsto (fun k ↦ ‖uSeq (ψ k)‖) Filter.atTop (nhds (1 : ℝ)) := by
      simpa [huSeq_norm] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ))
        Filter.atTop (nhds (1 : ℝ)))
    exact (tendsto_nhds_unique hconst_tendsto hnorm_tendsto).symm
  have hnorm_atTop :
      Filter.Tendsto (fun k ↦ ‖ySeq (φ (ψ k))‖) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun k ↦ ?_) tendsto_natCast_atTop_atTop
    have hk : (k : ℝ) ≤ (ψ k : ℝ) := by
      exact_mod_cast hψ.id_le k
    have hlarge := hφ_large (ψ k)
    linarith
  have hinv_tendsto_zero :
      Filter.Tendsto (fun k ↦ ‖ySeq (φ (ψ k))‖⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    hnorm_atTop.inv_tendsto_atTop
  have hχ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hz_subseq :
      Filter.Tendsto (fun k ↦ zSeq (φ (ψ k))) Filter.atTop (nhds z) :=
    hzSeq.comp hχ.tendsto_atTop
  have hfuSeq_tendsto_zero :
      Filter.Tendsto (fun k ↦ f (uSeq (ψ k))) Filter.atTop (nhds (0 : Fin n → ℝ)) := by
    -- Mapping the normalized sequence turns it into a vanishing scalar multiple of the convergent
    -- image sequence.
    simpa [uSeq, hySeq_map, LinearMap.map_smul] using hinv_tendsto_zero.smul hz_subseq
  have hf_tendsto :
      Filter.Tendsto (fun k ↦ f (uSeq (ψ k))) Filter.atTop (nhds (f u)) := by
    exact (LinearMap.continuous_of_finiteDimensional f).continuousAt.tendsto.comp hψ_tendsto
  have hu_kernel : f u = 0 := tendsto_nhds_unique hf_tendsto hfuSeq_tendsto_zero
  exact ⟨u, ψ, hψ, by simpa [uSeq] using hψ_tendsto, hu_nonneg, hu_kernel, hu_norm⟩

/-- Helper for Lemma 2.5: convergence to a unit vector forces the half-step perturbation norm to
eventually stay below `1`. -/
private theorem eventually_norm_sub_half_lt_one
    {u : Fin m → ℝ} {v : ℕ → Fin m → ℝ}
    (hv : Filter.Tendsto v Filter.atTop (nhds u))
    (hu_norm : ‖u‖ = 1) :
    ∀ᶠ k in Filter.atTop, ‖v k - (1 / 2 : ℝ) • u‖ < 1 := by
  have hnorm_tendsto :
      Filter.Tendsto (fun k ↦ ‖v k - (1 / 2 : ℝ) • u‖) Filter.atTop
        (nhds ‖u - (1 / 2 : ℝ) • u‖) := by
    exact continuous_norm.continuousAt.tendsto.comp (hv.sub tendsto_const_nhds)
  have hhalf : u - (1 / 2 : ℝ) • u = (1 / 2 : ℝ) • u := by
    ext i
    simp [Pi.sub_apply]
    ring
  have hlt : ‖u - (1 / 2 : ℝ) • u‖ < 1 := by
    rw [hhalf, norm_smul, hu_norm]
    norm_num
  exact hnorm_tendsto (Iio_mem_nhds hlt)

/- Helper for Lemma 2.5: bounded nonnegative preimages of a convergent image sequence admit a
nonnegative limit preimage of the limiting image point. -/
private theorem boundedNonnegativePreimages_hasLimitPreimage
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    {z : Fin n → ℝ} {zSeq : ℕ → Fin n → ℝ} {ySeq : ℕ → Fin m → ℝ}
    (hzSeq : Filter.Tendsto zSeq Filter.atTop (nhds z))
    (hySeq_nonneg : ∀ k, ySeq k ∈ Set.Ici (0 : Fin m → ℝ))
    (hySeq_map : ∀ k, f (ySeq k) = zSeq k)
    (hySeq_bounded : Bornology.IsBounded (Set.range ySeq)) :
    ∃ y ∈ Set.Ici (0 : Fin m → ℝ), f y = z := by
  obtain ⟨R, hR⟩ := hySeq_bounded.subset_closedBall (0 : Fin m → ℝ)
  have hySeq_ball : ∀ k, ySeq k ∈ Metric.closedBall 0 R := by
    intro k
    exact hR ⟨k, rfl⟩
  obtain ⟨y, hy_ball, φ, hφ, hφy⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : Fin m → ℝ) R) hySeq_ball
  have hy_nonneg : y ∈ Set.Ici (0 : Fin m → ℝ) := by
    -- Closedness of the orthant keeps the subsequential limit nonnegative.
    apply isClosed_Ici.mem_of_tendsto hφy
    exact Filter.Eventually.of_forall fun k => hySeq_nonneg (φ k)
  have hfcont : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hφy' : Filter.Tendsto (fun k ↦ ySeq (φ k)) Filter.atTop (nhds y) := hφy
  have hmap_subseq :
      Filter.Tendsto (fun k ↦ f (ySeq (φ k))) Filter.atTop (nhds (f y)) := by
    exact hfcont.continuousAt.tendsto.comp hφy'
  have hz_subseq : Filter.Tendsto (fun k ↦ zSeq (φ k)) Filter.atTop (nhds z) := by
    exact hzSeq.comp hφ.tendsto_atTop
  haveI : Filter.NeBot (Filter.atTop : Filter ℕ) := inferInstance
  have hy_map : f y = z := by
    -- The subsequence converges both through `f` and through the prescribed image equation.
    apply tendsto_nhds_unique hmap_subseq
    simpa [hySeq_map] using hz_subseq
  exact ⟨y, hy_nonneg, hy_map⟩

/- Helper for Lemma 2.5: minimal-norm nonnegative preimages of a convergent image sequence are
bounded. -/
private theorem minimalNormPreimageSequenceBounded
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    {z : Fin n → ℝ} {zSeq : ℕ → Fin n → ℝ} {ySeq : ℕ → Fin m → ℝ}
    (hzSeq : Filter.Tendsto zSeq Filter.atTop (nhds z))
    (hySeq_nonneg : ∀ k, ySeq k ∈ Set.Ici (0 : Fin m → ℝ))
    (hySeq_map : ∀ k, f (ySeq k) = zSeq k)
    (hySeq_min :
      ∀ k, ∀ y' ∈ Set.Ici (0 : Fin m → ℝ), f y' = zSeq k → ‖ySeq k‖ ≤ ‖y'‖) :
    Bornology.IsBounded (Set.range ySeq) := by
  -- Route correction: instead of the abandoned support-reduction route, normalize a large-norm
  -- subsequence, extract a nonnegative kernel direction, and contradict fiberwise minimality by a
  -- fixed half-step inside that kernel direction.
  classical
  by_contra hy_unbounded
  obtain ⟨φ, hφ, hφ_large⟩ :=
    existsLargeNormSubsequence_of_not_bounded hy_unbounded
  obtain ⟨u, ψ, hψ, hnorm_tendsto, hu_nonneg, hu_kernel, hu_norm⟩ :=
    existsNormalizedKernelLimit_of_largeNormSubsequence
      f hzSeq hySeq_nonneg hySeq_map φ hφ hφ_large
  let χ : ℕ → ℕ := φ ∘ ψ
  let normalized : ℕ → Fin m → ℝ := fun k ↦ ‖ySeq (χ k)‖⁻¹ • ySeq (χ k)
  let competitor : ℕ → Fin m → ℝ := fun k ↦ ySeq (χ k) - (‖ySeq (χ k)‖ / 2) • u
  have hnormalized_tendsto :
      Filter.Tendsto normalized Filter.atTop (nhds u) := by
    simpa [normalized, χ, Function.comp] using hnorm_tendsto
  have hnormalized_nonneg : ∀ k, normalized k ∈ Set.Ici (0 : Fin m → ℝ) := by
    intro k i
    -- The normalized subsequence stays in the orthant because the scale is nonnegative.
    simpa [normalized, χ, Pi.smul_apply] using
      mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (hySeq_nonneg (χ k) i)
  have hEventually_nonneg :
      ∀ᶠ k in Filter.atTop, normalized k - (1 / 2 : ℝ) • u ∈ Set.Ici (0 : Fin m → ℝ) :=
    eventually_sub_half_limit_mem_Ici hnormalized_tendsto hu_nonneg hnormalized_nonneg
  have hcompetitor_eq :
      ∀ k, competitor k = ‖ySeq (χ k)‖ • (normalized k - (1 / 2 : ℝ) • u) := by
    intro k
    have hpos : 0 < ‖ySeq (χ k)‖ := by
      have hk : 0 < (ψ k : ℝ) + 1 := by positivity
      exact lt_of_lt_of_le hk (hφ_large (ψ k))
    -- Rewrite the competitor as a positive scalar multiple of the normalized half-step.
    calc
      competitor k =
          ‖ySeq (χ k)‖ • normalized k - ‖ySeq (χ k)‖ • ((1 / 2 : ℝ) • u) := by
        dsimp [competitor]
        dsimp [normalized]
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, smul_smul]
        simp [χ, div_eq_mul_inv, mul_comm]
      _ = ‖ySeq (χ k)‖ • (normalized k - (1 / 2 : ℝ) • u) := by
        rw [smul_sub]
  have hEventually_competitor_nonneg :
      ∀ᶠ k in Filter.atTop, competitor k ∈ Set.Ici (0 : Fin m → ℝ) := by
    filter_upwards [hEventually_nonneg] with k hk i
    -- Multiplying an eventually nonnegative vector by a nonnegative norm keeps it feasible.
    have hscaled :
        ‖ySeq (χ k)‖ • (normalized k - (1 / 2 : ℝ) • u) ∈ Set.Ici (0 : Fin m → ℝ) := by
      exact fun j ↦ mul_nonneg (norm_nonneg _) (hk j)
    simpa [hcompetitor_eq k] using hscaled i
  have hEventually_norm_lt_one :
      ∀ᶠ k in Filter.atTop, ‖normalized k - (1 / 2 : ℝ) • u‖ < 1 :=
    eventually_norm_sub_half_lt_one hnormalized_tendsto hu_norm
  have hEventually_norm_drop :
      ∀ᶠ k in Filter.atTop, ‖competitor k‖ < ‖ySeq (χ k)‖ := by
    filter_upwards [hEventually_norm_lt_one] with k hk
    have hpos : 0 < ‖ySeq (χ k)‖ := by
      have hk' : 0 < (ψ k : ℝ) + 1 := by positivity
      exact lt_of_lt_of_le hk' (hφ_large (ψ k))
    -- The half-step reduces the norm by a factor strictly smaller than `1`.
    rw [hcompetitor_eq k, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simpa using mul_lt_mul_of_pos_left hk hpos
  have hcompetitor_map : ∀ k, f (competitor k) = zSeq (χ k) := by
    intro k
    -- The extracted limit lies in the kernel, so the competitor stays in the same fiber.
    calc
      f (competitor k) = f (ySeq (χ k)) - f ((‖ySeq (χ k)‖ / 2) • u) := by
        dsimp [competitor]
        rw [LinearMap.map_sub]
      _ = zSeq (χ k) - (‖ySeq (χ k)‖ / 2) • f u := by
        rw [hySeq_map, LinearMap.map_smul]
      _ = zSeq (χ k) := by simp [hu_kernel]
  have hFalse : ∀ᶠ k : ℕ in Filter.atTop, False := by
    filter_upwards [hEventually_competitor_nonneg, hEventually_norm_drop] with
      (k : ℕ) hk_nonneg hk_drop
    have hk_min : ‖ySeq (χ k)‖ ≤ ‖competitor k‖ :=
      hySeq_min (χ k) (competitor k) hk_nonneg (hcompetitor_map k)
    linarith
  rw [Filter.eventually_atTop] at hFalse
  rcases hFalse with ⟨a, ha⟩
  exact (ha a le_rfl).elim

/- Linear images of the finite-dimensional nonnegative orthant are closed. -/
private theorem closure_imageIci_subset_imageIci
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    closure (f '' Set.Ici (0 : Fin m → ℝ)) ⊆ f '' Set.Ici (0 : Fin m → ℝ) := by
  intro z hz
  obtain ⟨zSeq, hzSeq_mem, hzSeq_tendsto⟩ := mem_closure_iff_seq_limit.mp hz
  choose ySeq hySeq_nonneg hySeq_map hySeq_min using
    fun k ↦ existsMinNormNonnegativePreimage f (hzSeq_mem k)
  have hySeq_bounded :
      Bornology.IsBounded (Set.range ySeq) :=
    minimalNormPreimageSequenceBounded f hzSeq_tendsto hySeq_nonneg hySeq_map hySeq_min
  rcases
      boundedNonnegativePreimages_hasLimitPreimage f hzSeq_tendsto hySeq_nonneg hySeq_map
        hySeq_bounded with
    ⟨y, hy_nonneg, hy_map⟩
  -- The bounded minimal-preimage machinery produces an actual nonnegative preimage of `z`.
  exact ⟨y, hy_nonneg, hy_map⟩

/- The negative-transpose image cone is closed in finite dimensions. -/
private theorem negativeTransposeImage_isClosed
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed ((((PointedCone.positive ℝ (Fin m → ℝ)).map (-Aᵀ).mulVecLin :
      PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
  -- Rewrite once to the plain set image of the orthant, then apply the closed-image lemma.
  rw [positiveMap_eq_imageIci]
  exact (closure_subset_iff_isClosed).mp (closure_imageIci_subset_imageIci (-Aᵀ).mulVecLin)

-- Proof sketch: reduce this formulation to the first Farkas lemma by adjoining the inequality
-- `-dotProduct c x ≤ -1` to `A *ᵥ x ≤ 0`, and conversely evaluate the certificate
-- `Aᵀ *ᵥ y = c` on any `x` with `A *ᵥ x ≤ 0` to obtain `dotProduct c x ≤ 0` from the
-- coordinatewise nonnegativity of `y`.
/-- Lemma 2.5: Farkas's lemma in the implication form. For a real matrix `A` and vector `c`, the
implication `A x ≤ 0 → cᵀ x ≤ 0` for every `x` is equivalent to the existence of a nonnegative
vector `y` with `Aᵀ y = c`; here `ℝ^m_+` is rendered as `Set.Ici (0 : Fin m → ℝ)`. -/
theorem farkas_lemma_second_formulation
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) → dotProduct c x ≤ 0) ↔
      ∃ y ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ y = c := by
  constructor
  · intro hA
    by_contra hno
    let imageCone : ProperCone ℝ (Fin n → ℝ) :=
      ⟨(PointedCone.positive ℝ (Fin m → ℝ)).map (-Aᵀ).mulVecLin, negativeTransposeImage_isClosed A⟩
    have hnegc_notmem' :
        -c ∉ (imageCone : Set (Fin n → ℝ)) := by
      intro hc
      exact hno <| (neg_mem_negativeTransposeImage_iff c A).mp (by simpa [imageCone] using hc)
    obtain ⟨f, hf_nonneg, hfc_neg⟩ :=
      ProperCone.hyperplane_separation_point imageCone hnegc_notmem'
    let x : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm f.toLinearMap
    have hf_apply_dotProduct : ∀ v : Fin n → ℝ, f v = dotProduct x v := by
      intro v
      have hxeq : dotProductEquiv ℝ (Fin n) x = f.toLinearMap := by
        simp [x]
      have hxev := congrArg (fun g : Module.Dual ℝ (Fin n → ℝ) ↦ g v) hxeq
      simpa [dotProductEquiv] using hxev.symm
    have hx_dual :
        x ∈ PointedCone.dual (dotProductPairing n)
          ((((PointedCone.positive ℝ (Fin m → ℝ)).map (-Aᵀ).mulVecLin :
              PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
      intro z hz
      change 0 ≤ dotProduct z x
      rw [dotProduct_comm, ← hf_apply_dotProduct z]
      exact hf_nonneg z hz
    have hx_nonpos : A *ᵥ x ≤ (0 : Fin m → ℝ) :=
      (mem_dual_negativeTransposeImage_iff A x).mp hx_dual
    have hx_pos : 0 < dotProduct c x := by
      have hneg : dotProduct (-c) x < 0 := by
        rw [← dotProduct_comm x (-c), ← hf_apply_dotProduct (-c)]
        exact hfc_neg
      have hneg' : -(dotProduct c x) < 0 := by
        simpa [dotProduct_neg, dotProduct_comm] using hneg
      linarith
    exact (not_lt_of_ge (hA x hx_nonpos) hx_pos).elim
  · rintro ⟨y, hy_nonneg, hy_eq⟩ x hx
    have hy_nonneg' : (0 : Fin m → ℝ) ≤ y := hy_nonneg
    have hneg_mulVec_nonneg : (0 : Fin m → ℝ) ≤ -(A *ᵥ x) := by
      simpa using fun i ↦ neg_nonneg.mpr (hx i)
    have hpair_nonneg : 0 ≤ dotProduct y (-(A *ᵥ x)) := by
      exact dotProduct_nonneg_of_nonneg hy_nonneg' hneg_mulVec_nonneg
    have hpair_nonpos : dotProduct y (A *ᵥ x) ≤ 0 := by
      simpa [dotProduct_neg] using hpair_nonneg
    -- Rewrite the objective through the transpose certificate and close by coordinatewise
    -- nonnegativity.
    calc
      dotProduct c x = dotProduct (Aᵀ *ᵥ y) x := by rw [hy_eq]
      _ = dotProduct y (A *ᵥ x) := by rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      _ ≤ 0 := hpair_nonpos

/-- Bridge/view: the certificate in Lemma 2.5 is equivalently membership of `c` in the image of
the positive pointed cone under the transpose linear map `Aᵀ`. -/
theorem farkas_lemma_second_formulation_iff_mem_transpose_nonnegative_cone
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) → dotProduct c x ≤ 0) ↔
      c ∈ transpose_nonnegative_cone A := by
  rw [farkas_lemma_second_formulation, mem_transpose_nonnegative_cone]

end
