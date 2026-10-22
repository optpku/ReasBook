/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_4
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_14
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

section

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "𝕊" => symmetricMatrices n
local notation "symmetricEigenvalues" => symmetric_eigenvalue_function

local instance proposition7_4_frobeniusNormedAddCommGroup : NormedAddCommGroup Mₙ :=
  Matrix.frobeniusNormedAddCommGroup
local instance proposition7_4_frobeniusNormedSpace : NormedSpace ℝ Mₙ :=
  Matrix.frobeniusNormedSpace
local instance proposition7_4_frobeniusInnerProductSpace : InnerProductSpace ℝ Mₙ :=
  Matrix.frobeniusInnerProductSpace

/- Proposition 7.4 is `source-facing`: the textbook projects a symmetric matrix onto the
associated symmetric spectral set determined by an eigenvalue-side set `C`. The chapter already
owns the relevant abstractions: `IsAssociatedSymmetricSpectralSet` from Definition 7.14 records
the source-facing relation between `T ⊆ 𝕊^n` and `C ⊆ ℝ^n`, and its companion API already
turns that relation into the symmetric-spectral-function factorization of
`extendedIndicator T`. Theorem 7.3 then supplies the ambient matrix reconstruction map
`orthogonalDiagonalMap`. The only stable helper below is the thin codomain-change bridge
turning that ambient map into a `𝕊^n`-valued map. -/

/-- Bridge/view: the diagonal-conjugation map from Theorem 7.3 lands in `𝕊^n`. -/
noncomputable def orthogonalDiagonalMapToSymmetric
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Fin n → ℝ) → 𝕊 :=
  fun x ↦
    ⟨orthogonalDiagonalMap U x, by
      rw [mem_symmetricMatrices_iff]
      simp [orthogonalDiagonalMap_apply, Matrix.transpose_mul, mul_assoc]⟩

/-- Coercing `orthogonalDiagonalMapToSymmetric U x` to matrices recovers the ambient Chapter 7
owner `orthogonalDiagonalMap U x`. -/
@[simp] theorem orthogonalDiagonalMapToSymmetric_coe
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    ((orthogonalDiagonalMapToSymmetric U x : 𝕊) : Mₙ) = orthogonalDiagonalMap U x :=
  rfl

/-- Bridge/view: the Euclidean diagonal-conjugation map from Theorem 7.3 lands in `𝕊^n`. -/
noncomputable def orthogonalDiagonalMapEuclideanToSymmetric
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    Eₙ → 𝕊 :=
  fun x ↦
    ⟨orthogonalDiagonalMapEuclidean U x, by
      rw [mem_symmetricMatrices_iff]
      simp [orthogonalDiagonalMapEuclidean, orthogonalDiagonalMap_apply, Matrix.transpose_mul,
        mul_assoc]⟩

/-- Coercing `orthogonalDiagonalMapEuclideanToSymmetric U x` to matrices recovers the ambient
Chapter 7 owner `orthogonalDiagonalMapEuclidean U x`. -/
@[simp] theorem orthogonalDiagonalMapEuclideanToSymmetric_coe
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Eₙ) :
    ((orthogonalDiagonalMapEuclideanToSymmetric U x : 𝕊) : Mₙ) =
      orthogonalDiagonalMapEuclidean U x :=
  rfl

/-- Helper for Proposition 7.4: a permutation-symmetric indicator cannot distinguish the Chapter 7
owner `symmetricEigenvalues` from the local ordered-eigenvalue owner
`symmetric_eigenvalue_function`. -/
lemma extendedIndicator_symmetricEigenvalues_eq_extendedIndicator_symmetric_eigenvalue_function
    {C : Set (Fin n → ℝ)} (hC_perm : IsPermutationSymmetricFunction (extendedIndicator C))
    (Y : 𝕊) :
    extendedIndicator C (_root_.symmetricEigenvalues_7_23 Y) =
      extendedIndicator C (symmetric_eigenvalue_function Y) := by
  obtain ⟨σ, hσ⟩ := exists_eigenvalue_reindex_perm (n := n)
  -- Route correction: the two eigenvalue owners match only up to a fixed permutation, so the
  -- right bridge is permutation-symmetric evaluation of `extendedIndicator C`.
  calc
    extendedIndicator C (_root_.symmetricEigenvalues_7_23 Y) =
        extendedIndicator C (symmetric_eigenvalue_function Y ∘ σ) := by
          change extendedIndicator C (Y.property.isHermitian.eigenvalues) =
            extendedIndicator C (symmetric_eigenvalue_function Y ∘ σ)
          rw [hσ Y]
    _ = extendedIndicator C (symmetric_eigenvalue_function Y) := by
          simpa [permutationOrthogonalMatrix_smul] using
            hC_perm.map_smul (permutationOrthogonalMatrix σ) (Set.mem_range_self σ)
              (symmetric_eigenvalue_function Y)

/-- Helper for Proposition 7.4: membership in an associated symmetric spectral set is exactly the
eigenvalue-side membership condition. -/
lemma mem_associatedSymmetricSpectralSet_iff
    {T : Set 𝕊} {C : Set (Fin n → ℝ)} (hTC : IsAssociatedSymmetricSpectralSet T C) {Y : 𝕊} :
    Y ∈ T ↔ symmetric_eigenvalue_function Y ∈ C := by
  have hIndicator :
      extendedIndicator T Y = extendedIndicator C (symmetric_eigenvalue_function Y) := by
    -- First rewrite the associated-set factorization at `Y`, then remove the owner permutation.
    calc
      extendedIndicator T Y = extendedIndicator C (_root_.symmetricEigenvalues_7_23 Y) := by
        simpa [Function.comp] using congrArg (fun g : 𝕊 → EReal => g Y) hTC.2
      _ = extendedIndicator C (symmetric_eigenvalue_function Y) := by
        exact
          extendedIndicator_symmetricEigenvalues_eq_extendedIndicator_symmetric_eigenvalue_function
            hTC.1 Y
  -- Read membership off from the indicator values on each side.
  by_cases hYT : Y ∈ T
  · by_cases hYC : symmetric_eigenvalue_function Y ∈ C
    · simp [hYT, hYC]
    · simp [extendedIndicator, hYT, hYC] at hIndicator
  · by_cases hYC : symmetric_eigenvalue_function Y ∈ C
    · simp [extendedIndicator, hYT, hYC] at hIndicator
    · simp [hYT, hYC]

/-- Helper for Proposition 7.4: a nonempty associated eigenvalue set yields a nonempty associated
symmetric spectral set. -/
lemma nonempty_associatedSymmetricSpectralSet_of_nonempty
    {T : Set 𝕊} {C : Set (Fin n → ℝ)} (hTC : IsAssociatedSymmetricSpectralSet T C)
    (hC_nonempty : C.Nonempty) :
    T.Nonempty := by
  rcases hC_nonempty with ⟨x, hx⟩
  have hdesc :
      ∀ z : Fin n → ℝ, extendedIndicator C z = extendedIndicator C z↓ :=
    (isPermutationSymmetricFunction_iff_forall_eq_descendingRearrangement
      (extendedIndicator C)).1 hTC.1 |>.2
  have hxDesc : x↓ ∈ C := by
    -- Permutation symmetry transports the witness `x ∈ C` to the sorted representative `x↓`.
    have hval : extendedIndicator C x = extendedIndicator C x↓ := hdesc x
    by_cases hxDown : x↓ ∈ C
    · exact hxDown
    · simp [extendedIndicator, hx, hxDown] at hval
  let Y : 𝕊 := ⟨Matrix.diagonal (x↓), diagonal_mem_symmetricMatrices (x↓)⟩
  have hYeig : symmetric_eigenvalue_function Y = x↓ := by
    -- The sorted diagonal witness exposes exactly the sorted spectrum on its diagonal.
    simpa [Y] using
      diagonal_symmetric_eigenvalue_function_eq_of_antitone (x↓)
        (antitone_descendingRearrangement x)
  refine ⟨Y, ?_⟩
  -- The associated-set membership criterion now reduces to the diagonal witness `x↓ ∈ C`.
  rw [mem_associatedSymmetricSpectralSet_iff hTC]
  simpa [hYeig] using hxDesc

/-- Helper for Proposition 7.4: the Euclidean pullback `y ↦ δ_C(y.ofLp)` is the indicator of the
Euclidean realization `WithLp.toLp '' C`. -/
lemma extendedIndicator_ofLp_eq_extendedIndicator_toLpImage
    (C : Set (Fin n → ℝ)) :
    (fun y : Eₙ ↦ extendedIndicator C y.ofLp) =
      extendedIndicator (WithLp.toLp (p := (2 : ENNReal)) '' C) := by
  funext y
  by_cases hy : y.ofLp ∈ C
  · -- On points coming from `C`, both indicator functions are zero.
    have hyImage : y ∈ WithLp.toLp (p := (2 : ENNReal)) '' C := by
      refine ⟨y.ofLp, hy, ?_⟩
      simp
    simp [extendedIndicator, hy, hyImage]
  · -- Outside `C`, injectivity of `ofLp` rules out membership in the transported image.
    have hyImage : y ∉ WithLp.toLp (p := (2 : ENNReal)) '' C := by
      rintro ⟨x, hx, hxy⟩
      have hxeq : x = y.ofLp := by
        simpa using congrArg (WithLp.ofLp (p := (2 : ENNReal))) hxy
      exact hy (hxeq ▸ hx)
    simp [extendedIndicator, hy, hyImage]

/-- Helper for Proposition 7.4: the subtype spectral proximal set at a diagonalized symmetric
matrix is the orthogonal image of the Euclidean proximal set for the diagonal data. -/
lemma prox_subtypeSpectral_eq_image_orthogonalDiagonalMapEuclideanToSymmetric
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (X : 𝕊) (U : Matrix.orthogonalGroup (Fin n) ℝ) (d : Fin n → ℝ)
    (hdiag : X = orthogonalDiagonalMapToSymmetric U d) :
    prox[fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)] X =
      orthogonalDiagonalMapEuclideanToSymmetric U ''
        prox[fun y : Eₙ ↦ f y.ofLp] (WithLp.toLp (p := (2 : ENNReal)) d) := by
  let diagLp : Eₙ := WithLp.toLp (p := (2 : ENNReal)) d
  have hX_coe :
      ((X : 𝕊) : Mₙ).IsSymm := by
    exact mem_symmetricMatrices_iff.mp X.property
  have hdiag_coe : (X : Mₙ) = orthogonalDiagonalMap U d := by
    -- Coerce the subtype diagonalization hypothesis to the ambient matrix statement used below.
    simpa using congrArg (fun Z : 𝕊 => ((Z : 𝕊) : Mₙ)) hdiag
  have hclosedconv :=
    symmetric_spectral_function_closed_convex_on_subtype f hf_perm hf_closed hf_convex
  have hproper := symmetric_spectral_function_proper_on_subtype f hf_perm
  rcases prox_eq_singleton_of_proper_closed_convex
      (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) hproper hclosedconv.1 hclosedconv.2 X with
    ⟨Y0, hsubsingleton⟩
  have hambient :
      prox[symmetricSpectralLift f] (orthogonalDiagonalMap U d) = {(Y0 : Mₙ)} := by
    have hambient' : prox[symmetricSpectralLift f] (X : Mₙ) = {(Y0 : Mₙ)} := by
      -- Move the subtype singleton result to the ambient spectral lift by the canonical coercion
      -- bridge from `Theorem_7_3`.
      rw [prox_symmetricSpectralLift_eq_subtype_image f hf_perm (X : Mₙ) hX_coe,
        hsubsingleton, Set.image_singleton]
    simpa [hdiag_coe] using hambient'
  have hpullback :=
    theorem7_3_euclidean_pullback_proper_closed_convex f hf_perm hf_closed hf_convex
  rcases prox_eq_singleton_of_proper_closed_convex
      (fun y : Eₙ ↦ f y.ofLp) hpullback.1 hpullback.2.1 hpullback.2.2 diagLp with
    ⟨x0, hvecsingleton⟩
  have hY0_mem : (Y0 : Mₙ) ∈ prox[symmetricSpectralLift f] (orthogonalDiagonalMap U d) := by
    rw [hambient]
    simp
  have hdiag_mem :
      ((U : Mₙ)ᵀ * (Y0 : Mₙ) * (U : Mₙ)) ∈
        prox[symmetricSpectralLift f] (Matrix.diagonal d) := by
    -- Orthogonal conjugation transports the proximal point to the diagonal basis.
    exact (mem_prox_symmetricSpectralLift_orthogonal_conjugate_iff f U d (Y0 : Mₙ)).1 hY0_mem
  rcases diagonal_basis_prox_is_diagonal f hf_perm hf_closed hf_convex d hdiag_mem with ⟨w, hwdiag⟩
  have hdiag_mem' :
      Matrix.diagonal w ∈ prox[symmetricSpectralLift f] (Matrix.diagonal d) := by
    simpa [hwdiag] using hdiag_mem
  have hw_euclidean :
      WithLp.toLp (p := (2 : ENNReal)) w ∈ prox[fun y : Eₙ ↦ f y.ofLp] diagLp :=
    diagonal_mem_prox_euclidean_of_mem_prox_symmetricSpectralLift f hf_perm d w hdiag_mem'
  have hw_eq_x0 : WithLp.toLp (p := (2 : ENNReal)) w = x0 := by
    have hmem : WithLp.toLp (p := (2 : ENNReal)) w ∈ ({x0} : Set Eₙ) := by
      simpa [hvecsingleton, diagLp] using hw_euclidean
    simpa using hmem
  have hx0_ofLp : x0.ofLp = w := by
    simpa using (congrArg (fun y : Eₙ ↦ y.ofLp) hw_eq_x0).symm
  have hY0_eq_matrix :
      (Y0 : Mₙ) = orthogonalDiagonalMapEuclidean U x0 := by
    have hUUt : (U : Mₙ) * (U : Mₙ)ᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
    -- Reassemble the ambient proximal point from its diagonal form and the orthogonal basis.
    calc
      (Y0 : Mₙ)
          = (U : Mₙ) * (((U : Mₙ)ᵀ * (Y0 : Mₙ) * (U : Mₙ))) * (U : Mₙ)ᵀ := by
              calc
                (Y0 : Mₙ) = (((U : Mₙ) * (U : Mₙ)ᵀ) * (Y0 : Mₙ)) * ((U : Mₙ) * (U : Mₙ)ᵀ) := by
                              simp [hUUt]
                _ = (U : Mₙ) * (((U : Mₙ)ᵀ * (Y0 : Mₙ) * (U : Mₙ))) * (U : Mₙ)ᵀ := by
                      simp [mul_assoc]
      _ = (U : Mₙ) * Matrix.diagonal w * (U : Mₙ)ᵀ := by
            rw [hwdiag]
      _ = orthogonalDiagonalMapEuclidean U x0 := by
            simp [orthogonalDiagonalMapEuclidean, orthogonalDiagonalMap_apply, hx0_ofLp]
  have hY0_eq :
      Y0 = orthogonalDiagonalMapEuclideanToSymmetric U x0 := by
    -- The subtype equality is proved at the cheaper ambient matrix layer.
    apply Subtype.ext
    simpa [orthogonalDiagonalMapEuclideanToSymmetric_coe] using hY0_eq_matrix
  -- Both the subtype proximal set and the Euclidean proximal set are singletons, so the desired
  -- image identity follows by rewriting those singleton representatives.
  calc
    prox[fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)] X = {Y0} := hsubsingleton
    _ = {orthogonalDiagonalMapEuclideanToSymmetric U x0} := by rw [hY0_eq]
    _ = orthogonalDiagonalMapEuclideanToSymmetric U ''
          prox[fun y : Eₙ ↦ f y.ofLp] diagLp := by
            rw [hvecsingleton, Set.image_singleton]

-- Proof sketch: rewrite the indicator of the source-facing set `T` through the associated-set
-- hypothesis `hTC`, convert the projection sets into proximal sets of the corresponding indicator
-- functions, apply the Chapter 7 proximal formula from Theorem 7.3 to `extendedIndicator C`, and
-- then return to the projection notation on both sides.
/-- Proposition 7.4: let `T ⊆ 𝕊^n` be associated to `C ⊆ ℝ^n` in the sense of
Definition 7.14. If `C` is closed and convex, then the projection set of `X` onto `T`
is obtained by conjugating the Euclidean projection set of the ordered eigenvalue vector
`λ(X)` onto the canonical Euclidean realization of `C` by the same orthogonal diagonalizer
`U`. This is the chapter's set-valued form of equation `(7.6)`. -/
theorem projection_mapping_eq_image_projection_mapping_eigenvalues_of_associatedSet
    {T : Set 𝕊} {C : Set (Fin n → ℝ)} (hTC : IsAssociatedSymmetricSpectralSet T C)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (X : 𝕊) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hdiag : X = orthogonalDiagonalMapToSymmetric U (symmetricEigenvalues X)) :
    P[T] X =
      orthogonalDiagonalMapEuclideanToSymmetric U ''
        P[WithLp.toLp (p := (2 : ENNReal)) '' C]
          (WithLp.toLp (p := (2 : ENNReal)) (symmetricEigenvalues X)) := by
  by_cases hC_nonempty : C.Nonempty
  · have hT_nonempty :
        T.Nonempty :=
      nonempty_associatedSymmetricSpectralSet_of_nonempty hTC hC_nonempty
    have hC_image_nonempty : (WithLp.toLp (p := (2 : ENNReal)) '' C).Nonempty := by
      rcases hC_nonempty with ⟨x, hx⟩
      exact ⟨WithLp.toLp (p := (2 : ENNReal)) x, ⟨x, hx, rfl⟩⟩
    have hC_closed_indicator :
        LowerSemicontinuous (extendedIndicator C) :=
      (extendedIndicator_lowerSemicontinuous_iff_isClosed C).2 hC_closed
    have hC_convex_indicator :
        is_convex_function (extendedIndicator C) :=
      extendedIndicator_isConvexFunction_of_convex C hC_convex
    have hIndicatorFactor :
        extendedIndicator T = fun Y : 𝕊 ↦ extendedIndicator C (symmetricEigenvalues Y) := by
      funext Y
      -- Route correction: the associated-set factorization is stated with the Chapter 7 owner
      -- `_root_.symmetricEigenvalues_7_23`, so we rewrite it through the
      -- permutation-symmetric bridge.
      calc
        extendedIndicator T Y = extendedIndicator C (_root_.symmetricEigenvalues_7_23 Y) := by
          simpa [Function.comp] using congrArg (fun g : 𝕊 → EReal => g Y) hTC.2
        _ = extendedIndicator C (symmetricEigenvalues Y) := by
          exact
            extendedIndicator_symmetricEigenvalues_eq_extendedIndicator_symmetric_eigenvalue_function
              hTC.1 Y
    -- Convert both projection mappings to proximal mappings, then apply the subtype spectral
    -- proximal formula for `extendedIndicator C`.
    rw [← prox_extendedIndicator_eq_projection_mapping T hT_nonempty X, hIndicatorFactor]
    rw [← prox_extendedIndicator_eq_projection_mapping
      (WithLp.toLp (p := (2 : ENNReal)) '' C) hC_image_nonempty
      (WithLp.toLp (p := (2 : ENNReal)) (symmetricEigenvalues X))]
    rw [← extendedIndicator_ofLp_eq_extendedIndicator_toLpImage (n := n) C]
    exact
      prox_subtypeSpectral_eq_image_orthogonalDiagonalMapEuclideanToSymmetric
        (f := extendedIndicator C) hTC.1 hC_closed_indicator hC_convex_indicator X U
        (symmetricEigenvalues X) hdiag
  · have hC_empty : C = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hC_nonempty ⟨x, hx⟩)
      · simp
    have hT_empty : T = ∅ := by
      ext Y
      constructor
      · intro hY
        have hEig : symmetric_eigenvalue_function Y ∈ C :=
          (mem_associatedSymmetricSpectralSet_iff hTC).1 hY
        simp [hC_empty] at hEig
      · simp
    have hC_image_empty : WithLp.toLp (p := (2 : ENNReal)) '' C = ∅ := by
      simp [hC_empty]
    -- In the empty branch, both projection mappings are definitionally empty sets.
    simp [projection_mapping, hT_empty, hC_image_empty]

end
