/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.ENat.Basic

public section

open Filter
open scoped Topology

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- Definition 2.15. A singular system for a compact operator `K : H₁ →L[𝕜] H₂` is ordered
countable data of right singular vectors, singular values, and left singular vectors, indexed by
an initial segment of `ℕ∞`, such that the right singular vectors form a Hilbert basis of `K.kerᗮ`,
the left singular vectors form a Hilbert basis of `K.range.topologicalClosure`, the singular values
are positive and nonincreasing, and `K` and `K†` intertwine the two bases by those singular
values. -/
structure SingularSystem (K : H₁ →L[𝕜] H₂) where
  /-- The length of the ordered singular data, viewed as an initial segment of `ℕ∞`. -/
  length : ℕ∞
  /-- The left singular vectors indexed by `j < length` form a Hilbert basis of
  `K.range.topologicalClosure`. -/
  leftBasis : HilbertBasis {j : ℕ∞ // j < length} 𝕜 K.range.topologicalClosure
  /-- The right singular vectors indexed by `j < length` form a Hilbert basis of `K.kerᗮ`. -/
  rightBasis : HilbertBasis {j : ℕ∞ // j < length} 𝕜 K.kerᗮ
  /-- The singular value attached to each index. -/
  singularValue : {j : ℕ∞ // j < length} → ℝ
  /-- The operator underlying a singular system is compact. -/
  isCompact : IsCompactOperator K
  /-- Every singular value is positive. -/
  singularValue_pos : ∀ j, 0 < singularValue j
  /-- The singular values are nonincreasing in the index order. -/
  singularValue_antitone : Antitone singularValue
  /-- `K` sends each right singular vector to the corresponding scaled left singular vector. -/
  map_right :
    ∀ j, K (rightBasis j : H₁) = (singularValue j : 𝕜) • (leftBasis j : H₂)
  /-- `K†` sends each left singular vector to the corresponding scaled right singular vector. -/
  adjoint_map_left :
    ∀ j, K.adjoint (leftBasis j : H₂) = (singularValue j : 𝕜) • (rightBasis j : H₁)

namespace SingularSystem

variable {K : H₁ →L[𝕜] H₂}

/-- The index type of the ordered singular data of a singular system. -/
abbrev Index (S : SingularSystem K) : Type := {j : ℕ∞ // j < S.length}

/-- Every index in `S.Index` lies below `S.length`. -/
theorem index_lt_length (S : SingularSystem K) (j : S.Index) :
    (j : ℕ∞) < S.length := by
  -- The index type is the defining subtype `{j : ℕ∞ // j < S.length}`.
  exact j.2

/-- The fields `S.leftBasis` and `S.rightBasis` encode the two orthonormal-basis clauses of
Definition 2.15, and this theorem bundles the remaining defining conditions. -/
theorem spec (S : SingularSystem K) :
    IsCompactOperator K ∧
      (∀ j : S.Index, 0 < S.singularValue j) ∧
      Antitone S.singularValue ∧
      (∀ j : S.Index,
        K (S.rightBasis j : H₁) = (S.singularValue j : 𝕜) • (S.leftBasis j : H₂)) ∧
      (∀ j : S.Index,
        K.adjoint (S.leftBasis j : H₂) = (S.singularValue j : 𝕜) • (S.rightBasis j : H₁)) := by
  -- This simply repackages the structure fields that are not already basis data.
  exact
    ⟨S.isCompact, S.singularValue_pos, S.singularValue_antitone, S.map_right,
      S.adjoint_map_left⟩

/-- If `S.length = ⊤`, every natural number determines an index of `S`. -/
theorem nat_lt_length_of_length_eq_top
    (S : SingularSystem K) (h_length : S.length = ⊤) (n : ℕ) :
    (n : ℕ∞) < S.length := by
  -- After rewriting `S.length` to `⊤`, this is the standard `ENat` bound on natural casts.
  simp [h_length, ENat.coe_lt_top]

/-- If `S.length = ⊤`, the natural number `n` determines the corresponding index of `S`. -/
def natIndex (S : SingularSystem K) (h_length : S.length = ⊤) (n : ℕ) : S.Index :=
  ⟨(n : ℕ∞), nat_lt_length_of_length_eq_top S h_length n⟩

@[simp] theorem coe_natIndex
    (S : SingularSystem K) (h_length : S.length = ⊤) (n : ℕ) :
    (S.natIndex h_length n : ℕ∞) = n := by
  simp [natIndex]

/-- Helper for Definition 2.15: under `S.length = ⊤`, the canonical indices `S.natIndex h_length n`
are strictly increasing with `n`. -/
theorem natIndex_strictMono
    (S : SingularSystem K) (h_length : S.length = ⊤) :
    StrictMono (S.natIndex h_length) := by
  intro m n hmn
  -- The subtype order is inherited from `ℕ∞`, and natural casts preserve strict inequalities.
  simpa [natIndex] using hmn

/-- Helper for Definition 2.15: finite singular length makes the singular-index type finite. -/
theorem finiteIndexOfLengthNeTop
    (S : SingularSystem K) (h_length : S.length ≠ ⊤) :
    Finite S.Index := by
  rcases ENat.ne_top_iff_exists.mp h_length with ⟨n, hn⟩
  have hfinite : Finite {j : ℕ∞ // j < (n : ℕ∞)} := by
    -- Rewrite the `ℕ∞`-subtype to the finite initial segment `{m : ℕ // m < n}`.
    let e : {j : ℕ∞ // j < (n : ℕ∞)} ≃ {m : ℕ // m < n} :=
      { toFun := fun j => ⟨ENat.lift (j : ℕ∞) (lt_of_lt_of_le j.2 le_top), by simpa using j.2⟩
        invFun := fun m => ⟨(m : ℕ∞), by simpa using m.2⟩
        left_inv := by
          intro j
          ext
          simp
        right_inv := by
          intro m
          ext
          simp }
    exact Finite.of_equiv {m : ℕ // m < n} e.symm
  simpa [Index, hn] using hfinite

/-- Helper for Definition 2.15: finite singular length forces
`K.range.topologicalClosure` to be finite-dimensional. -/
theorem finiteDimensionalRangeClosureOfLengthNeTop
    (S : SingularSystem K) (h_length : S.length ≠ ⊤) :
    FiniteDimensional 𝕜 K.range.topologicalClosure := by
  classical
  -- A finite Hilbert basis upgrades to a finite orthonormal basis, hence to a basis.
  haveI : Finite S.Index := S.finiteIndexOfLengthNeTop h_length
  -- Local instance justification (finite indexing): `HilbertBasis.toOrthonormalBasis` needs a
  -- `Fintype` on `S.Index`, obtained noncomputably from the proved `Finite` bridge.
  letI : Fintype S.Index := Fintype.ofFinite S.Index
  exact (S.leftBasis.toOrthonormalBasis.toBasis).finiteDimensional_of_finite

/-- If `K.range.topologicalClosure` is infinite-dimensional, the singular data are indexed by all
natural numbers, i.e. `S.length = ⊤`. -/
theorem length_eq_top_of_infiniteRange
    (S : SingularSystem K)
    (h_infinite : ¬ FiniteDimensional 𝕜 K.range.topologicalClosure) :
    S.length = ⊤ := by
  by_contra h_length
  -- Finite singular length would give a finite basis for the closed range.
  exact h_infinite (S.finiteDimensionalRangeClosureOfLengthNeTop h_length)

/-- Helper for Definition 2.15: distinct canonical singular vectors satisfy a Pythagorean
distance formula after applying `K`. -/
theorem normSubMapNatIndex_sq
    (S : SingularSystem K)
    (h_length : S.length = ⊤) {m n : ℕ} (h_ne : m ≠ n) :
    ‖K (S.rightBasis (S.natIndex h_length m) : H₁) -
        K (S.rightBasis (S.natIndex h_length n) : H₁)‖ *
      ‖K (S.rightBasis (S.natIndex h_length m) : H₁) -
        K (S.rightBasis (S.natIndex h_length n) : H₁)‖ =
      S.singularValue (S.natIndex h_length m) * S.singularValue (S.natIndex h_length m) +
        S.singularValue (S.natIndex h_length n) * S.singularValue (S.natIndex h_length n) := by
  let jm := S.natIndex h_length m
  let jn := S.natIndex h_length n
  have h_idx : jm ≠ jn := by
    intro h_eq
    apply h_ne
    exact (S.natIndex_strictMono h_length).injective h_eq
  have hm_norm : ‖(S.leftBasis jm : H₂)‖ = 1 := by
    simpa using S.leftBasis.orthonormal.norm_eq_one jm
  have hn_norm : ‖(S.leftBasis jn : H₂)‖ = 1 := by
    simpa using S.leftBasis.orthonormal.norm_eq_one jn
  have h_inner : inner 𝕜 (S.leftBasis jm : H₂) (S.leftBasis jn : H₂) = 0 := by
    simpa [jm, jn] using (S.leftBasis.orthonormal.2 h_idx)
  -- Rewrite the images using the singular-system identities.
  rw [S.map_right jm, S.map_right jn]
  -- The scaled left singular vectors remain orthogonal, so the norm square splits.
  have h_scaled :
      inner 𝕜 ((S.singularValue jm : 𝕜) • (S.leftBasis jm : H₂))
          (-((S.singularValue jn : 𝕜) • (S.leftBasis jn : H₂))) = 0 := by
    rw [inner_neg_right, inner_smul_left, inner_smul_right, h_inner]
    simp
  have h_pythagorean :
      ‖((S.singularValue jm : 𝕜) • (S.leftBasis jm : H₂)) +
          -((S.singularValue jn : 𝕜) • (S.leftBasis jn : H₂))‖ *
        ‖((S.singularValue jm : 𝕜) • (S.leftBasis jm : H₂)) +
            -((S.singularValue jn : 𝕜) • (S.leftBasis jn : H₂))‖ =
      ‖(S.singularValue jm : 𝕜) • (S.leftBasis jm : H₂)‖ *
        ‖(S.singularValue jm : 𝕜) • (S.leftBasis jm : H₂)‖ +
      ‖-((S.singularValue jn : 𝕜) • (S.leftBasis jn : H₂))‖ *
        ‖-((S.singularValue jn : 𝕜) • (S.leftBasis jn : H₂))‖ := by
    exact
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        ((S.singularValue jm : 𝕜) • (S.leftBasis jm : H₂))
        (-((S.singularValue jn : 𝕜) • (S.leftBasis jn : H₂)))
        h_scaled
  simpa [sub_eq_add_neg, hm_norm, hn_norm, norm_smul, norm_neg, RCLike.norm_ofReal,
    Real.norm_of_nonneg, le_of_lt, S.singularValue_pos] using h_pythagorean

/-- Under the infinite-length hypothesis, the singular values along the canonical `ℕ`-indexed
sequence `n ↦ S.natIndex h_length n` tend to `0`, as in Definition 2.15 (2.18). -/
theorem tendsto_zero_of_length_eq_top
    (S : SingularSystem K)
    (h_length : S.length = ⊤) :
    Tendsto (fun n : ℕ ↦ S.singularValue (S.natIndex h_length n)) Filter.atTop (𝓝 0) := by
  let s : ℕ → ℝ := S.singularValue ∘ S.natIndex h_length
  let x : ℕ → H₂ := fun n => K (S.rightBasis (S.natIndex h_length n) : H₁)
  have hs_antitone : Antitone s := by
    -- The natural-number indexing inherits the singular-value monotonicity from `S.Index`.
    exact S.singularValue_antitone.comp_monotone (S.natIndex_strictMono h_length).monotone
  have hcompactImage : IsCompact (closure (K '' Metric.closedBall (0 : H₁) 1)) := by
    -- Compactness of `K` makes the image of the unit closed ball relatively compact.
    simpa using S.isCompact.isCompact_closure_image_closedBall 1
  have hx_mem : ∀ n, x n ∈ closure (K '' Metric.closedBall (0 : H₁) 1) := by
    intro n
    -- Each right singular vector has norm `1`, hence lies in the unit closed ball.
    refine subset_closure ?_
    refine ⟨(S.rightBasis (S.natIndex h_length n) : H₁), ?_, rfl⟩
    have hnorm : ‖(S.rightBasis (S.natIndex h_length n) : H₁)‖ = 1 := by
      exact S.rightBasis.orthonormal.norm_eq_one (S.natIndex h_length n)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    simp [hnorm]
  obtain ⟨y, _, φ, hφ_mono, hφ_tendsto⟩ := hcompactImage.tendsto_subseq hx_mem
  have hφsucc_tendsto : Tendsto (fun n : ℕ ↦ x (φ (n + 1))) atTop (𝓝 y) := by
    -- Shifting a convergent subsequence preserves its limit.
    exact hφ_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
  have hdiffNorm : Tendsto (fun n : ℕ ↦ ‖x (φ n) - x (φ (n + 1))‖) atTop (𝓝 0) := by
    -- Consecutive terms of a convergent subsequence have vanishing differences.
    simpa using (hφ_tendsto.sub hφsucc_tendsto).norm
  have hsubseq_zero : Tendsto (fun n : ℕ ↦ s (φ n)) atTop (𝓝 0) := by
    -- Pythagorean separation bounds each singular value by a difference of subsequence terms.
    refine squeeze_zero (fun n => le_of_lt (S.singularValue_pos _)) ?_ hdiffNorm
    intro n
    have hsq :
        ‖x (φ n) - x (φ (n + 1))‖ * ‖x (φ n) - x (φ (n + 1))‖ =
          s (φ n) * s (φ n) + s (φ (n + 1)) * s (φ (n + 1)) := by
      simpa [s, x] using
        S.normSubMapNatIndex_sq h_length (m := φ n) (n := φ (n + 1))
          (by exact (hφ_mono (Nat.lt_succ_self n)).ne)
    have hpos₁ : 0 < s (φ n) := S.singularValue_pos _
    have hpos₂ : 0 < s (φ (n + 1)) := S.singularValue_pos _
    nlinarith [hsq, norm_nonneg (x (φ n) - x (φ (n + 1))), le_of_lt hpos₁, le_of_lt hpos₂]
  -- An antitone real sequence is determined by any subsequence with the candidate limit.
  exact
    (tendsto_iff_tendsto_subseq_of_antitone hs_antitone hφ_mono.tendsto_atTop).2 <|
      by simpa [s]

end SingularSystem

end ContinuousLinearMap
