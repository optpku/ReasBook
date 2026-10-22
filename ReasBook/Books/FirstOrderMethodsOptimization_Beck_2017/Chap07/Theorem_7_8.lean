/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_30
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_33
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_8
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_10
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open Function Matrix
open scoped Matrix

noncomputable section

section

variable {n : ℕ}

local notation "𝕊" => symmetricMatrices n
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "symmetricEigenvalues" => symmetric_eigenvalue_function

local instance instTheorem78NormedAddCommGroupMatrix : NormedAddCommGroup Mₙ :=
  Matrix.frobeniusNormedAddCommGroup
local instance instTheorem78NormedSpaceMatrix : NormedSpace ℝ Mₙ :=
  Matrix.frobeniusNormedSpace
local instance instTheorem78InnerProductSpaceMatrix : InnerProductSpace ℝ Mₙ :=
  Matrix.frobeniusInnerProductSpace

/- Theorem 7.8 is `source-facing`: it compares lower semicontinuity and convexity of a
permutation-symmetric profile `f : ℝ^n → (-∞, ∞]` with the same properties of its symmetric
spectral lift `f ∘ λ` on `𝕊^n`. The reusable owners
`diagonal_comp_perm_eq_orthogonal_conjugate`,
`orthogonal_conjugate_diagonal_charpoly`,
`diagonal_symmetric_eigenvalue_function_eq_of_antitone`,
`exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function`, and
`symmetric_spectral_diagonal_pullback_eq` already live in `Theorem_7_2` and `Theorem_7_3`; this
file reuses those declarations and adds the continuity companion theorem that Theorem 7.8 needs
explicitly. -/

/-- The diagonal embedding `x ↦ diag(x)` from `ℝ^n` to `𝕊^n` is continuous. -/
lemma continuous_diagonal_symmetricMatrices :
    Continuous
      (fun x : Fin n → ℝ ↦
        (⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩ : 𝕊)) := by
  exact continuous_id.matrix_diagonal.subtype_mk _

/-- Helper for Theorem 7.8: the `0/1` profile selecting the first `k` ordered coordinates. -/
def topEigenvalueIndicator (k : Fin (n + 1)) : Fin n → ℝ :=
  fun i ↦ if i.1 < k.1 then 1 else 0

/-- Helper for Theorem 7.8: the first `k` ordered eigenvalues of `X` summed together. -/
def spectralPartialSum (k : Fin (n + 1)) (X : 𝕊) : ℝ :=
  ∑ i : Fin n with i.1 < k.1, symmetricEigenvalues X i

-- Proof sketch: the indicator drops every coordinate past `k`, so the dot product keeps exactly
-- the first `k` entries of the ordered spectrum.
/-- Helper for Theorem 7.8: the partial sum of the first `k` ordered eigenvalues is the dot
product with the corresponding `0/1` indicator. -/
lemma spectralPartialSum_eq_dotProduct_indicator (k : Fin (n + 1)) (X : 𝕊) :
    spectralPartialSum k X =
      dotProduct (topEigenvalueIndicator k) (symmetricEigenvalues X) := by
  -- Expand the dot product and simplify the `0/1` filter coordinatewise.
  rw [spectralPartialSum, dotProduct, Finset.sum_filter]
  simp [topEigenvalueIndicator]

-- Proof sketch: once the later index has value `0`, every earlier index must also have value `0`;
-- otherwise both values are `1`.
/-- Helper for Theorem 7.8: the `0/1` projector profile is antitone. -/
lemma topEigenvalueIndicator_antitone (k : Fin (n + 1)) :
    Antitone (topEigenvalueIndicator (n := n) k) := by
  intro i j hij
  by_cases hj : j.1 < k.1
  · have hi : i.1 < k.1 := lt_of_le_of_lt (show i.1 ≤ j.1 by simpa using hij) hj
    simp [topEigenvalueIndicator, hi, hj]
  · by_cases hi : i.1 < k.1
    · simp [topEigenvalueIndicator, hi, hj]
    · simp [topEigenvalueIndicator, hi, hj]

-- Proof sketch: the `(i + 1)`-prefix indicator contains exactly one more `1` than the `i`-prefix,
-- namely at the coordinate `i` itself.
/-- Helper for Theorem 7.8: consecutive prefix indicators differ by the standard basis vector at
`i`. -/
lemma topEigenvalueIndicator_succ_sub_eq_single (i : Fin n) :
    (fun j : Fin n ↦
      topEigenvalueIndicator (n := n) ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j -
        topEigenvalueIndicator (n := n) ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩ j) =
      fun j : Fin n ↦ if j = i then 1 else 0 := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [topEigenvalueIndicator]
  · have hne : j.1 ≠ i.1 := fun h ↦ hji (Fin.ext h)
    cases lt_or_gt_of_ne hne with
    | inl hjlt =>
        have hjlt_succ : j.1 < i.1 + 1 := Nat.lt_succ_of_lt hjlt
        simp [topEigenvalueIndicator, hji, hjlt, hjlt_succ]
    | inr hijlt =>
        have hnot_succ : ¬ j.1 < i.1 + 1 := not_lt_of_ge (Nat.succ_le_of_lt hijlt)
        have hnot : ¬ j.1 < i.1 := not_lt_of_ge (Nat.le_of_lt hijlt)
        simp [topEigenvalueIndicator, hji, hnot, hnot_succ]

-- Proof sketch: the Euclidean `ℓ₂` norm square of the indicator is the count of its `1` entries,
-- namely `k`.
/-- Helper for Theorem 7.8: the `0/1` projector profile has Euclidean `ℓ₂` norm `√k`. -/
lemma norm_topEigenvalueIndicator (k : Fin (n + 1)) :
    ‖WithLp.toLp (p := (2 : ENNReal)) (topEigenvalueIndicator (n := n) k)‖ = Real.sqrt k := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq,
    Real.sq_sqrt (show 0 ≤ ((k : ℕ) : ℝ) by exact_mod_cast Nat.zero_le k.1)]
  · calc
      ∑ i, (WithLp.toLp (p := (2 : ENNReal)) (topEigenvalueIndicator k)).ofLp i ^ 2
          = ∑ i : Fin n, if i.1 < k.1 then (1 : ℝ) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases h : i.1 < k.1
              · simp [topEigenvalueIndicator, h]
              · simp [topEigenvalueIndicator, h]
      _ = k := by
            have hrange :
                (∑ i : Fin n, if i.1 < k.1 then (1 : ℝ) else 0) =
                  (Finset.range n).sum (fun j : ℕ ↦ if j < k.1 then (1 : ℝ) else 0) := by
              simpa using
                (Fin.sum_univ_eq_sum_range (n := n)
                  (f := fun j : ℕ ↦ if j < k.1 then (1 : ℝ) else 0))
            have hk_le : k.1 ≤ n := Nat.le_of_lt_succ k.2
            have hfilter :
                (Finset.range n).filter (fun j : ℕ ↦ j < k.1) = Finset.range k.1 := by
              ext j
              constructor
              · intro hj
                exact Finset.mem_range.mpr ((Finset.mem_filter.mp hj).2)
              · intro hj
                refine Finset.mem_filter.mpr ?_
                refine ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mp hj⟩
                exact lt_of_lt_of_le (Finset.mem_range.mp hj) hk_le
            rw [hrange]
            rw [Finset.sum_ite]
            simp [hfilter]

-- Proof sketch: mathlib already identifies the Frobenius norm of a diagonal matrix with the
-- Euclidean `ℓ₂` norm of its diagonal entries.
/-- Helper for Theorem 7.8: the Frobenius norm of a diagonal matrix is the Euclidean `ℓ₂` norm of
its diagonal vector. -/
lemma norm_diagonal_eq_norm (x : Fin n → ℝ) :
    ‖(Matrix.diagonal x : Mₙ)‖ = ‖WithLp.toLp (p := (2 : ENNReal)) x‖ := by
  -- Use the Frobenius-diagonal norm bridge directly instead of recomputing the entrywise sum.
  simpa using Matrix.frobenius_norm_diagonal x

-- Proof sketch: diagonalize `X` in an ordered eigenbasis, use Frobenius-norm invariance under the
-- corresponding orthogonal conjugation, and then collapse the diagonal case to the `ℓ₂` norm of
-- the ordered spectrum.
/-- Helper for Theorem 7.8: the ordered eigenvalue vector has the same Euclidean `ℓ₂` norm as the
ambient symmetric matrix in Frobenius norm. -/
lemma norm_symmetricEigenvalues_eq (X : 𝕊) :
    ‖WithLp.toLp (p := (2 : ENNReal)) (symmetricEigenvalues X)‖ = ‖X‖ := by
  obtain ⟨U, hX⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function X
  let D : Mₙ := Matrix.diagonal (symmetricEigenvalues X)
  have hnorm : ‖(X : Mₙ)‖ = ‖D‖ := by
    -- Conjugating `D` by the transpose orthogonal group element reconstructs `X`.
    simpa [D, hX, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      frobenius_norm_orthogonal_conjugate_eq (star U) D
  -- After diagonalization, the matrix norm is the Euclidean norm of the diagonal.
  calc
    ‖WithLp.toLp (p := (2 : ENNReal)) (symmetricEigenvalues X)‖ = ‖D‖ := by
      simpa [D] using (norm_diagonal_eq_norm (symmetricEigenvalues X)).symm
    _ = ‖X‖ := hnorm.symm

-- Proof sketch: combine the dot-product description of the partial sum with Cauchy--Schwarz, then
-- substitute the exact norms of the indicator and the ordered spectrum.
/-- Helper for Theorem 7.8: the sum of the first `k` ordered eigenvalues is bounded by
`√k ‖X‖_F`. -/
lemma spectralPartialSum_le_sqrt_mul_norm (k : Fin (n + 1)) (X : 𝕊) :
    spectralPartialSum k X ≤ Real.sqrt k * ‖X‖ := by
  have habs :
      |dotProduct (topEigenvalueIndicator k) (symmetricEigenvalues X)| ≤
        ‖WithLp.toLp (p := (2 : ENNReal)) (topEigenvalueIndicator k)‖ *
          ‖WithLp.toLp (p := (2 : ENNReal)) (symmetricEigenvalues X)‖ := by
    -- Move the finite vectors into the canonical Euclidean `ℓ₂` model and apply Cauchy--Schwarz.
    simpa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] using
      (abs_real_inner_le_norm
        (WithLp.toLp (p := (2 : ENNReal)) (topEigenvalueIndicator k))
        (WithLp.toLp (p := (2 : ENNReal)) (symmetricEigenvalues X)))
  -- Bound the partial sum by its absolute value and then apply Cauchy--Schwarz.
  rw [spectralPartialSum_eq_dotProduct_indicator]
  calc
    dotProduct (topEigenvalueIndicator k) (symmetricEigenvalues X)
      ≤ |dotProduct (topEigenvalueIndicator k) (symmetricEigenvalues X)| := le_abs_self _
    _ ≤ ‖WithLp.toLp (p := (2 : ENNReal)) (topEigenvalueIndicator k)‖ *
          ‖WithLp.toLp (p := (2 : ENNReal)) (symmetricEigenvalues X)‖ := habs
    _ = Real.sqrt k * ‖X‖ := by
          rw [norm_topEigenvalueIndicator, norm_symmetricEigenvalues_eq]

-- Proof sketch: rewrite the difference of two consecutive partial sums as the dot product against
-- the difference of the corresponding prefix indicators, then collapse that difference to the
-- standard basis vector at `i`.
/-- Helper for Theorem 7.8: consecutive partial sums isolate the `i`-th ordered eigenvalue. -/
lemma spectralPartialSum_succ_sub_eq_coordinate (i : Fin n) (X : 𝕊) :
    spectralPartialSum ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ X -
        spectralPartialSum ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩ X =
      symmetricEigenvalues X i := by
  rw [spectralPartialSum_eq_dotProduct_indicator, spectralPartialSum_eq_dotProduct_indicator,
    dotProduct, dotProduct, ← Finset.sum_sub_distrib]
  -- Factor the common eigenvalue coordinate and collapse the indicator difference to the basis
  -- vector at `i`.
  simp_rw [← sub_mul]
  have hsingle (j : Fin n) :
      topEigenvalueIndicator (n := n) ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j -
          topEigenvalueIndicator (n := n) ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩ j =
        if j = i then 1 else 0 := by
    simpa using congrFun (topEigenvalueIndicator_succ_sub_eq_single (n := n) i) j
  simp_rw [hsingle]
  simp

-- Proof sketch: diagonalize `X`, then use the same eigenbasis to build the `0/1` spectral
-- projector realizing the sum of the first `k` ordered eigenvalues by the trace pairing.
/-- Helper for Theorem 7.8: every partial sum of ordered eigenvalues is realized by tracing
against a symmetric matrix whose ordered spectrum is the matching `0/1` projector profile. -/
lemma exists_topEigenvalueIndicator_trace_witness
    (k : Fin (n + 1)) (X : 𝕊) :
    ∃ Y : 𝕊,
      symmetricEigenvalues Y = topEigenvalueIndicator k ∧
        Matrix.trace ((X : Mₙ) * (Y : Mₙ)) = spectralPartialSum k X := by
  obtain ⟨U, hX⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function X
  let Y : 𝕊 :=
    ⟨(U : Mₙ) * Matrix.diagonal (topEigenvalueIndicator k) * (U : Mₙ)ᵀ,
      orthogonal_conjugate_diagonal_mem U (topEigenvalueIndicator k)⟩
  have hspec : symmetricEigenvalues Y = topEigenvalueIndicator k := by
    -- The `0/1` diagonal is already ordered, so conjugation does not change its ordered spectrum.
    simpa [Y] using
      orthogonal_diagonal_symmetric_eigenvalue_function_eq_of_antitone U
        (topEigenvalueIndicator k) (topEigenvalueIndicator_antitone k)
  refine ⟨Y, hspec, ?_⟩
  have htrace :=
    trace_orthogonal_diagonal_mul_eq_dotProduct_symmetric_eigenvalue_function U X hX
      (topEigenvalueIndicator k)
  -- Commute the trace so the Chapter 7 diagonalization formula applies directly.
  calc
    Matrix.trace ((X : Mₙ) * (Y : Mₙ)) = Matrix.trace ((Y : Mₙ) * (X : Mₙ)) := by
      rw [Matrix.trace_mul_comm]
    _ = dotProduct (topEigenvalueIndicator k) (symmetricEigenvalues X) := by
      simpa [Y] using htrace
    _ = spectralPartialSum k X := by
      rw [spectralPartialSum_eq_dotProduct_indicator]

-- Proof sketch: Fan's inequality bounds every trace pairing by the dot product of ordered
-- eigenvalue vectors, and the witness spectrum rewrites that dot product as the relevant partial
-- sum.
/-- Helper for Theorem 7.8: tracing against a symmetric matrix with `0/1` ordered spectrum is
always bounded above by the corresponding partial sum of ordered eigenvalues. -/
lemma trace_le_spectralPartialSum_of_indicator_spectrum
    (k : Fin (n + 1)) (X Y : 𝕊)
    (hY : symmetricEigenvalues Y = topEigenvalueIndicator k) :
    Matrix.trace ((X : Mₙ) * (Y : Mₙ)) ≤ spectralPartialSum k X := by
  calc
    Matrix.trace ((X : Mₙ) * (Y : Mₙ))
      ≤ dotProduct (symmetricEigenvalues X) (symmetricEigenvalues Y) :=
        fan_inequality_trace_le_dotProduct_symmetric_eigenvalue_function X Y
    _ = dotProduct (topEigenvalueIndicator k) (symmetricEigenvalues X) := by
          rw [hY, dotProduct_comm]
    _ = spectralPartialSum k X := by
          rw [← spectralPartialSum_eq_dotProduct_indicator]

-- Proof sketch: realize the left-hand partial sum by its spectral projector witness, split the
-- trace into the base point plus the increment, and bound the increment by the universal
-- `√k ‖X - Z‖` estimate.
/-- Helper for Theorem 7.8: the partial-sum map satisfies the one-sided Lipschitz estimate needed
for `LipschitzWith.of_le_add_mul`. -/
lemma spectralPartialSum_le_add_sqrt_mul_norm
    (k : Fin (n + 1)) (X Z : 𝕊) :
    spectralPartialSum k X ≤ spectralPartialSum k Z + Real.sqrt k * ‖X - Z‖ := by
  obtain ⟨Y, hYspec, hYtrace⟩ := exists_topEigenvalueIndicator_trace_witness k X
  have hsplit :
      Matrix.trace ((X : Mₙ) * (Y : Mₙ)) =
        Matrix.trace ((Z : Mₙ) * (Y : Mₙ)) +
          Matrix.trace ((((X - Z : 𝕊) : Mₙ) * (Y : Mₙ))) := by
    -- Rewrite `X` as `Z + (X - Z)` and use linearity of the trace.
    have hdecomp : (X : Mₙ) = (Z : Mₙ) + ((X - Z : 𝕊) : Mₙ) := by
      ext i j
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hdecomp, Matrix.add_mul, Matrix.trace_add]
  have hinc :
      Matrix.trace ((((X - Z : 𝕊) : Mₙ) * (Y : Mₙ))) ≤ Real.sqrt k * ‖X - Z‖ := by
    exact
      (trace_le_spectralPartialSum_of_indicator_spectrum k (X - Z : 𝕊) Y hYspec).trans
        (spectralPartialSum_le_sqrt_mul_norm k (X - Z : 𝕊))
  -- The projector witness for `X` stays admissible at `Z`, and the remaining increment is
  -- controlled by the norm estimate.
  calc
    spectralPartialSum k X = Matrix.trace ((X : Mₙ) * (Y : Mₙ)) := hYtrace.symm
    _ = Matrix.trace ((Z : Mₙ) * (Y : Mₙ)) +
          Matrix.trace ((((X - Z : 𝕊) : Mₙ) * (Y : Mₙ))) := hsplit
    _ ≤ spectralPartialSum k Z + Real.sqrt k * ‖X - Z‖ := by
          exact add_le_add
            (trace_le_spectralPartialSum_of_indicator_spectrum k Z Y hYspec)
            hinc

-- Proof sketch: the previous one-sided estimate is exactly the metric-space criterion for a
-- real-valued Lipschitz function.
/-- Helper for Theorem 7.8: each ordered-eigenvalue partial-sum map is globally Lipschitz. -/
lemma lipschitzWith_spectralPartialSum (k : Fin (n + 1)) :
    LipschitzWith ⟨Real.sqrt k, Real.sqrt_nonneg _⟩ (spectralPartialSum k : 𝕊 → ℝ) := by
  refine LipschitzWith.of_le_add_mul ⟨Real.sqrt k, Real.sqrt_nonneg _⟩ ?_
  intro X Z
  -- Repackage the one-sided norm estimate as the metric-space Lipschitz condition.
  simpa [dist_eq_norm, Real.dist_eq] using spectralPartialSum_le_add_sqrt_mul_norm k X Z

/-- Helper for Theorem 7.8: each ordered eigenvalue coordinate
`X ↦ symmetricEigenvalues X i` is continuous on `𝕊^n`. -/
lemma continuous_symmetricEigenvalueCoordinate (i : Fin n) :
    Continuous (fun X : 𝕊 ↦ symmetricEigenvalues X i) := by
  let kPrev : Fin (n + 1) := ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩
  let kNext : Fin (n + 1) := ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
  have hPrev : Continuous (spectralPartialSum kPrev : 𝕊 → ℝ) :=
    (lipschitzWith_spectralPartialSum kPrev).continuous
  have hNext : Continuous (spectralPartialSum kNext : 𝕊 → ℝ) :=
    (lipschitzWith_spectralPartialSum kNext).continuous
  -- Route correction: rather than searching for a missing owner theorem for individual ordered
  -- eigenvalues, write `λᵢ` as the difference of consecutive Lipschitz partial sums.
  have hcoord :
      (fun X : 𝕊 ↦ symmetricEigenvalues X i) =
        fun X : 𝕊 ↦ spectralPartialSum kNext X - spectralPartialSum kPrev X := by
    funext X
    simpa [kPrev, kNext] using (spectralPartialSum_succ_sub_eq_coordinate i X).symm
  rw [hcoord]
  exact hNext.sub hPrev

/-- The ordered eigenvalue map `λ : 𝕊^n → ℝ^n` is continuous. -/
lemma continuous_symmetricEigenvalues :
    Continuous (symmetricEigenvalues : 𝕊 → Fin n → ℝ) := by
  -- Assemble the vector-valued continuity from the coordinatewise continuity helper.
  exact continuous_pi fun i ↦ continuous_symmetricEigenvalueCoordinate i

/-- The diagonal embedding carries segments in `ℝ^n` to segments in `𝕊^n`. -/
lemma diagonal_symmetricMatrices_segment
    (x y : Fin n → ℝ) (t : ℝ) :
    (⟨Matrix.diagonal (t • x + (1 - t) • y),
        diagonal_mem_symmetricMatrices (t • x + (1 - t) • y)⟩ : 𝕊) =
      t • (⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩ : 𝕊) +
        (1 - t) • (⟨Matrix.diagonal y, diagonal_mem_symmetricMatrices y⟩ : 𝕊) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.diagonal, hij]

/-- Convexity plus permutation symmetry makes `f` decrease under every doubly stochastic
averaging. -/
lemma convex_permutation_symmetric_le_of_doubly_stochastic
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hfconv : is_convex_function f) {x : Fin n → ℝ} (hx : x ∈ effective_domain f)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    f (P *ᵥ x) ≤ f x := by
  obtain ⟨w, hw_nonneg, hw_sum, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  have hconv_toReal : ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function hfconv (fun z hz ↦ hf.ne_bot z)
  have hperm_eq :
      ∀ σ : Equiv.Perm (Fin n), f ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = f x := by
    intro σ
    exact hf.map_smul (permutationOrthogonalMatrix σ) (Set.mem_range_self σ) x
  have hperm_mem :
      ∀ σ : Equiv.Perm (Fin n),
        ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) ∈ effective_domain f := by
    intro σ
    rw [mem_effective_domain, hperm_eq σ]
    simpa [mem_effective_domain] using hx
  have hmulVec_decomp :
      (∑ σ, (w σ • (σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ))) *ᵥ x =
        ∑ σ, w σ • ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) := by
    rw [sum_mulVec]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    rw [smul_mulVec]
  have hPx_mem : P *ᵥ x ∈ effective_domain f := by
    have hconv_dom : Convex ℝ (effective_domain f) :=
      effective_domain_convex_of_is_convex_function hfconv
    rw [← hwP, hmulVec_decomp]
    exact hconv_dom.sum_mem (fun σ _ ↦ hw_nonneg σ) (by simpa using hw_sum)
      (fun σ _ ↦ hperm_mem σ)
  have h_toReal : (f (P *ᵥ x)).toReal ≤ (f x).toReal := by
    rw [← hwP, hmulVec_decomp]
    calc
      (f (∑ σ, w σ • ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x))).toReal
          ≤ ∑ σ, w σ • (f ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)).toReal := by
            exact hconv_toReal.map_sum_le (fun σ _ ↦ hw_nonneg σ) (by simpa using hw_sum)
              (fun σ _ ↦ hperm_mem σ)
      _ = ∑ σ, w σ • (f x).toReal := by
            refine Finset.sum_congr rfl ?_
            intro σ hσ
            rw [hperm_eq σ]
      _ = (∑ σ, w σ) * (f x).toReal := by
            simp [smul_eq_mul, Finset.sum_mul]
      _ = (f x).toReal := by
            rw [hw_sum, one_mul]
  have hx_top : f x ≠ ⊤ := by
    exact ne_of_lt (by simpa [mem_effective_domain] using hx)
  have hPx_top : f (P *ᵥ x) ≠ ⊤ := by
    exact ne_of_lt (by simpa [mem_effective_domain] using hPx_mem)
  have hx_bot : f x ≠ ⊥ := hf.ne_bot x
  have hPx_bot : f (P *ᵥ x) ≠ ⊥ := hf.ne_bot (P *ᵥ x)
  rw [← EReal.coe_toReal hPx_top hPx_bot, ← EReal.coe_toReal hx_top hx_bot]
  exact_mod_cast h_toReal

/-- The diagonal of an orthogonal conjugate of a symmetric matrix is a doubly stochastic image of
its ordered eigenvalue vector. -/
lemma diag_orthogonal_conjugate_eq_doubly_stochastic_mul_symmetric_eigenvalues
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (X : 𝕊) :
    ∃ P : Mₙ, P ∈ doublyStochastic ℝ (Fin n) ∧
      Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) = P *ᵥ symmetricEigenvalues X := by
  obtain ⟨V, hX⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function X
  let Q : Matrix.orthogonalGroup (Fin n) ℝ := star U * V
  let P : Mₙ := fun i j : Fin n ↦ (Q i j)^2
  have hP : P ∈ doublyStochastic ℝ (Fin n) := by
    simpa [P] using orthogonal_entrywise_sq_mem_doubly_stochastic Q
  have hQ : ((Q : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) = (U : Mₙ)ᵀ * (V : Mₙ) := by
    change star (U : Mₙ) * (V : Mₙ) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨P, hP, ?_⟩
  ext i
  have hconj :
      ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) =
        (Q : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * ((Q : Mₙ)ᵀ) := by
    calc
      ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) =
          ((U : Mₙ)ᵀ) *
            ((V : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * (V : Mₙ)ᵀ) *
            (U : Mₙ) := by
              rw [hX]
      _ = ((U : Mₙ)ᵀ * (V : Mₙ)) * Matrix.diagonal (symmetricEigenvalues X) *
            ((V : Mₙ)ᵀ * (U : Mₙ)) := by
              simp [mul_assoc]
      _ = (Q : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * ((Q : Mₙ)ᵀ) := by
              simp [hQ, mul_assoc, Matrix.transpose_mul]
  calc
    Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) i =
        (((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) i i) := by
          rfl
    _ = (((Q : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * ((Q : Mₙ)ᵀ)) i i) := by
          rw [hconj]
    _ = ∑ j, (Q i j)^2 * symmetricEigenvalues X j := by
          rw [diagonal_conj_entry (symmetricEigenvalues X) Q i]
    _ = ∑ j, P i j * symmetricEigenvalues X j := by
          simp [P]
    _ = (P *ᵥ symmetricEigenvalues X) i := by
          simp [Matrix.mulVec, dotProduct]

/-- After diagonalizing the midpoint matrix, its ordered eigenvalue vector is the convex
combination of the two conjugated diagonals in that eigenbasis. -/
lemma symmetric_eigenvalue_segment_eq_conjugate_diagonal_combo
    (X Y : 𝕊) (t : ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hZ :
      (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) =
        (U : Mₙ) * Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) *
          (U : Mₙ)ᵀ) :
    symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊) =
      t • Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) +
        (1 - t) • Matrix.diag ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ)) := by
  have hUtU : ((U : Mₙ)ᵀ * (U : Mₙ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hdiag :
      Matrix.diag
          ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) =
        symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊) := by
    have hconj :
        ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) =
          Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) := by
      let D : Mₙ := Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊))
      calc
        ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) =
            ((U : Mₙ)ᵀ) *
              ((U : Mₙ) * D * (U : Mₙ)ᵀ) *
              (U : Mₙ) := by
                rw [hZ]
        _ = (((U : Mₙ)ᵀ * (U : Mₙ)) * D) * ((U : Mₙ)ᵀ * (U : Mₙ)) := by
                simp [mul_assoc]
        _ = D := by
                rw [hUtU, Matrix.mul_one]
                simp
        _ = Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) := by
                rfl
    simpa using congrArg Matrix.diag hconj
  calc
    symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊) =
        Matrix.diag ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) := by
          symm
          exact hdiag
    _ = Matrix.diag
          (t • ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) +
            (1 - t) • ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ))) := by
          simp [mul_add, add_mul, mul_assoc]
    _ = t • Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) +
          (1 - t) • Matrix.diag ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ)) := by
          ext i
          simp [Matrix.diag, Pi.add_apply, Pi.smul_apply]

/-- Jensen's inequality for the symmetric spectral lift, obtained by diagonalizing the midpoint
matrix and comparing the resulting diagonals to the ordered spectra via doubly stochastic
averaging. -/
lemma spectral_segment_jensen_step
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hfconv : is_convex_function f) (X Y : 𝕊)
    (hx : X ∈ effective_domain (f ∘ symmetricEigenvalues))
    (hy : Y ∈ effective_domain (f ∘ symmetricEigenvalues))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) ≤
      (t : EReal) * f (symmetricEigenvalues X) +
        (((1 - t : ℝ) : EReal)) * f (symmetricEigenvalues Y) := by
  let Z : 𝕊 := t • X + (1 - t) • Y
  obtain ⟨U, hZ⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function Z
  let a : Fin n → ℝ := Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ))
  let b : Fin n → ℝ := Matrix.diag ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ))
  obtain ⟨PX, hPX_ds, hPX⟩ :=
    diag_orthogonal_conjugate_eq_doubly_stochastic_mul_symmetric_eigenvalues U X
  obtain ⟨PY, hPY_ds, hPY⟩ :=
    diag_orthogonal_conjugate_eq_doubly_stochastic_mul_symmetric_eigenvalues U Y
  have hspec :
      symmetricEigenvalues Z = t • a + (1 - t) • b := by
    simpa [Z, a, b] using
      symmetric_eigenvalue_segment_eq_conjugate_diagonal_combo X Y t U hZ
  have hx_vec : symmetricEigenvalues X ∈ effective_domain f := by
    simpa [mem_effective_domain, Function.comp] using hx
  have hy_vec : symmetricEigenvalues Y ∈ effective_domain f := by
    simpa [mem_effective_domain, Function.comp] using hy
  have ha_le : f a ≤ f (symmetricEigenvalues X) := by
    rw [show a = PX *ᵥ symmetricEigenvalues X by simpa [a] using hPX]
    exact convex_permutation_symmetric_le_of_doubly_stochastic f hf hfconv hx_vec hPX_ds
  have hb_le : f b ≤ f (symmetricEigenvalues Y) := by
    rw [show b = PY *ᵥ symmetricEigenvalues Y by simpa [b] using hPY]
    exact convex_permutation_symmetric_le_of_doubly_stochastic f hf hfconv hy_vec hPY_ds
  have ha_eff : a ∈ effective_domain f := by
    exact lt_of_le_of_lt ha_le (by simpa [mem_effective_domain] using hx_vec)
  have hb_eff : b ∈ effective_domain f := by
    exact lt_of_le_of_lt hb_le (by simpa [mem_effective_domain] using hy_vec)
  have hseg :
      f (t • a + (1 - t) • b) ≤
        (t : EReal) * f a + (((1 - t : ℝ) : EReal)) * f b :=
    (is_convex_function_iff_segment_ineq.mp hfconv) a ha_eff b hb_eff ht
  have ht_nonneg : 0 ≤ (t : EReal) := by
    exact_mod_cast ht.1
  have hone_sub_nonneg : 0 ≤ (((1 - t : ℝ) : EReal)) := by
    exact_mod_cast sub_nonneg.2 ht.2
  calc
    f (symmetricEigenvalues Z) = f (t • a + (1 - t) • b) := by rw [hspec]
    _ ≤ (t : EReal) * f a + (((1 - t : ℝ) : EReal)) * f b := hseg
    _ ≤ (t : EReal) * f (symmetricEigenvalues X) +
          (((1 - t : ℝ) : EReal)) * f (symmetricEigenvalues Y) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left ha_le ht_nonneg)
              (mul_le_mul_of_nonneg_left hb_le hone_sub_nonneg)

/-- If `f` is convex and permutation symmetric, then its symmetric spectral lift `f ∘ λ` is
convex on `𝕊^n`. -/
lemma symmetric_spectral_convex_forward
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hfconv : is_convex_function f) :
    is_convex_function (f ∘ symmetricEigenvalues) := by
  let _ : IsProperExtendedRealFunction (f ∘ symmetricEigenvalues) :=
    by
      simpa [Function.comp] using symmetric_spectral_function_proper_on_subtype f hf
  rw [is_convex_function_iff_segment_ineq]
  intro X hx Y hy t ht
  exact spectral_segment_jensen_step f hf hfconv X Y hx hy ht

/-- Pulling the symmetric spectral lift back along the diagonal embedding preserves convexity. -/
lemma symmetric_spectral_convex_reverse
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hF_convex : is_convex_function (f ∘ symmetricEigenvalues)) :
    is_convex_function f := by
  let _ : IsProperExtendedRealFunction (f ∘ symmetricEigenvalues) :=
    by
      simpa [Function.comp] using symmetric_spectral_function_proper_on_subtype f hf
  rw [is_convex_function_iff_segment_ineq] at hF_convex ⊢
  intro x hx y hy t ht
  let X : 𝕊 := ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩
  let Y : 𝕊 := ⟨Matrix.diagonal y, diagonal_mem_symmetricMatrices y⟩
  have hXeq : (f ∘ symmetricEigenvalues) X = f x := by
    simpa [Function.comp, X] using symmetric_spectral_diagonal_pullback_eq f hf x
  have hYeq : (f ∘ symmetricEigenvalues) Y = f y := by
    simpa [Function.comp, Y] using symmetric_spectral_diagonal_pullback_eq f hf y
  have hX : X ∈ effective_domain (f ∘ symmetricEigenvalues) := by
    rw [mem_effective_domain, hXeq]
    simpa [mem_effective_domain] using hx
  have hY : Y ∈ effective_domain (f ∘ symmetricEigenvalues) := by
    rw [mem_effective_domain, hYeq]
    simpa [mem_effective_domain] using hy
  have hseg := hF_convex X hX Y hY ht
  have hcomboeq :
      (f ∘ symmetricEigenvalues)
          (⟨Matrix.diagonal (t • x + (1 - t) • y),
            diagonal_mem_symmetricMatrices (t • x + (1 - t) • y)⟩ : 𝕊) =
        f (t • x + (1 - t) • y) := by
    simpa [Function.comp] using
      symmetric_spectral_diagonal_pullback_eq f hf (t • x + (1 - t) • y)
  rw [← diagonal_symmetricMatrices_segment x y t, hcomboeq, hXeq, hYeq] at hseg
  exact hseg

/-- Pulling the symmetric spectral lift back along the diagonal embedding preserves lower
semicontinuity. -/
lemma symmetric_spectral_lowerSemicontinuous_reverse
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hF_closed : LowerSemicontinuous (f ∘ symmetricEigenvalues)) :
    LowerSemicontinuous f := by
  have hpull :
      ((f ∘ symmetricEigenvalues) ∘
        fun x : Fin n → ℝ ↦
          (⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩ : 𝕊)) = f := by
    funext x
    simpa [Function.comp] using symmetric_spectral_diagonal_pullback_eq f hf x
  have hcomp :
      LowerSemicontinuous
        (((f ∘ symmetricEigenvalues) ∘
          fun x : Fin n → ℝ ↦
            (⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩ : 𝕊))) :=
    hF_closed.comp continuous_diagonal_symmetricMatrices
  rw [hpull] at hcomp
  exact hcomp

-- Proof sketch: the reverse implication is the diagonal pullback just above, while the forward
-- implication is continuous precomposition by the ordered eigenvalue map `λ`.
/-- Theorem 7.8 (1): for a permutation-symmetric extended-real-valued function on `ℝ^n`, the
spectral lift `f ∘ λ` on `𝕊^n` is lower semicontinuous if and only if `f` is lower
semicontinuous. Here `λ` denotes `symmetricEigenvalues`. -/
theorem symmetric_spectral_function_lowerSemicontinuous_iff
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f) :
    LowerSemicontinuous (f ∘ symmetricEigenvalues) ↔ LowerSemicontinuous f := by
  constructor
  · intro hF_closed
    exact symmetric_spectral_lowerSemicontinuous_reverse f hf hF_closed
  · intro hf_closed
    simpa [Function.comp] using hf_closed.comp continuous_symmetricEigenvalues

-- Proof sketch: the forward implication is Jensen's inequality on the symmetric spectral lift,
-- using diagonalization of the midpoint matrix and doubly stochastic averaging; the reverse
-- implication pulls the matrix inequality back along diagonal matrices.
/-- Theorem 7.8 (2): for a permutation-symmetric extended-real-valued function on `ℝ^n`, the
spectral lift `f ∘ λ` on `𝕊^n` is convex if and only if `f` is convex. Here convexity is
expressed by `is_convex_function` and `λ` denotes `symmetricEigenvalues`. -/
theorem symmetric_spectral_function_is_convex_function_iff
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f) :
    is_convex_function (f ∘ symmetricEigenvalues) ↔ is_convex_function f := by
  constructor
  · intro hF_convex
    exact symmetric_spectral_convex_reverse f hf hF_convex
  · intro hf_convex
    exact symmetric_spectral_convex_forward f hf hf_convex

end
