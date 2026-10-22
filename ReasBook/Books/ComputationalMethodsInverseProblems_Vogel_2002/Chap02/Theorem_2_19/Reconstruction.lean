/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A3.Comparison
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Mul

public section

noncomputable section

namespace ContinuousLinearMap.SingularSystem

universe u v

variable {H₁ : Type u} {H₂ : Type v}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable {K : H₁ →L[ℝ] H₂}

/-- The `(2.24)` reconstruction series is a bounded linear map on `H₂`. -/
theorem isBoundedLinearMap_tsum_filterSeries
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C) :
    IsBoundedLinearMap ℝ (fun g : H₂ ↦ ∑' j, S.filterSeries w g j) := by
  rcases h_bound with ⟨C, hC0, hC⟩
  have hmul :
      ∀ j : S.Index,
        ‖ContinuousLinearMap.mul ℝ ℝ (w (S.singularValue j ^ 2) / S.singularValue j)‖ ≤ C := by
    intro j
    rw [ContinuousLinearMap.opNorm_mul_apply]
    simpa [Real.norm_eq_abs, abs_div] using hC (S.singularValue j) (S.singularValue_pos j)
  let D : lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    lp.mapCLM 2
      (fun j => ContinuousLinearMap.mul ℝ ℝ (w (S.singularValue j ^ 2) / S.singularValue j))
      hC0
      hmul
  let L :
      H₂ →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    (↑S.leftBasis.repr.toContinuousLinearEquiv :
      K.range.topologicalClosure →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2) ∘L
      K.range.topologicalClosure.orthogonalProjectionOnto
  let R :
      lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] H₁ :=
    K.kerᗮ.subtypeL ∘L
      (↑S.rightBasis.repr.symm.toContinuousLinearEquiv :
        lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] K.kerᗮ)
  let T : H₂ →L[ℝ] H₁ := R ∘L (D ∘L L)
  have hsumT : ∀ g : H₂, HasSum (S.filterSeries w g) (T g) := by
    intro g
    have hsumSubtype :
        HasSum
          (fun j : S.Index ↦
            (D (S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g)) j) •
              (S.rightBasis j : K.kerᗮ))
          (S.rightBasis.repr.symm
            (D (S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g)))) := by
      simpa using
        S.rightBasis.hasSum_repr_symm
          (D (S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g)))
    have hsumH1 := hsumSubtype.mapL K.kerᗮ.subtypeL
    refine HasSum.congr_fun (by simpa [T, R, L] using hsumH1) ?_
    intro j
    have hcoeff :
        S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g) j =
          inner ℝ (S.leftBasis j : H₂) g := by
      rw [HilbertBasis.repr_apply_apply]
      exact K.range.topologicalClosure.inner_orthogonalProjectionOnto_eq_of_mem_left
        (S.leftBasis j) g
    rw [S.filterSeries_apply]
    simp [D, hcoeff]
  have htsum : (fun g : H₂ ↦ ∑' j, S.filterSeries w g j) = T := by
    funext g
    exact (hsumT g).tsum_eq
  exact htsum.symm ▸ T.isBoundedLinearMap

/-- The `(2.24)` reconstruction series is additive in the datum argument. -/
theorem map_add_tsum_filterSeries
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C) :
    ∀ g h : H₂,
      (∑' j, S.filterSeries w (g + h) j) =
        (∑' j, S.filterSeries w g j) + (∑' j, S.filterSeries w h j) := by
  intro g h
  let T : H₂ →L[ℝ] H₁ :=
    (isBoundedLinearMap_tsum_filterSeries S w h_bound).toContinuousLinearMap
  -- Compare the three series through the continuous linear map bundled from the owner witness.
  change T (g + h) = T g + T h
  exact T.map_add g h

/-- The `(2.24)` reconstruction series is homogeneous in the datum argument. -/
theorem map_smul_tsum_filterSeries
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C) :
    ∀ (c : ℝ) (g : H₂),
      (∑' j, S.filterSeries w (c • g) j) =
        c • (∑' j, S.filterSeries w g j) := by
  intro c g
  let T : H₂ →L[ℝ] H₁ :=
    (isBoundedLinearMap_tsum_filterSeries S w h_bound).toContinuousLinearMap
  -- Compare the two series through the continuous linear map bundled from the owner witness.
  change T (c • g) = c • T g
  exact T.map_smulₛₗ c g

/-- The `(2.24)` reconstruction series defines a continuous map on `H₂`. -/
theorem continuous_tsum_filterSeries
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C) :
    Continuous (fun g : H₂ ↦ ∑' j, S.filterSeries w g j) := by
  -- Continuity is inherited from the bounded-linearity owner.
  exact (isBoundedLinearMap_tsum_filterSeries S w h_bound).continuous

/-- The bundled reconstruction operator defined by the singular-system filter series `(2.24)`. -/
def reconstructionOperator
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C) :
    H₂ →L[ℝ] H₁ :=
  (isBoundedLinearMap_tsum_filterSeries S w h_bound).toContinuousLinearMap

/-- The family of reconstruction operators obtained from `(2.24)` by varying the filter
parameter. -/
@[expose]
def reconstructionFamily {ι : Type*}
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C) :
    ι → H₂ →L[ℝ] H₁ :=
  fun α ↦ S.reconstructionOperator (w α) (h_bound α)

/-- Evaluating `S.reconstructionOperator w h_bound` gives the `tsum` of the filter series. -/
theorem reconstructionOperator_apply
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C) (g : H₂) :
    S.reconstructionOperator w h_bound g = ∑' j, S.filterSeries w g j := by
  -- Evaluate the continuous linear map bundled from the bounded-linearity witness.
  rw [reconstructionOperator]
  exact IsBoundedLinearMap.toContinuousLinearMap_apply
    (hf := isBoundedLinearMap_tsum_filterSeries S w h_bound)
    g

/-- Evaluating the reconstruction family at `α` recovers the corresponding reconstruction
operator. -/
@[simp] theorem reconstructionFamily_apply {ι : Type*}
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C) (α : ι) :
    S.reconstructionFamily w h_bound α = S.reconstructionOperator (w α) (h_bound α) := rfl

/-- `S.reconstructionOperator w h_bound` satisfies the Chapter 7 filter-series specification. -/
theorem hasFilterRepresentation_reconstructionOperator
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C) :
    S.HasFilterRepresentation w (S.reconstructionOperator w h_bound) := by
  rcases h_bound with ⟨C, hC0, hC⟩
  have hmul :
      ∀ j : S.Index,
        ‖ContinuousLinearMap.mul ℝ ℝ (w (S.singularValue j ^ 2) / S.singularValue j)‖ ≤ C := by
    intro j
    rw [ContinuousLinearMap.opNorm_mul_apply]
    simpa [Real.norm_eq_abs, abs_div] using hC (S.singularValue j) (S.singularValue_pos j)
  let D : lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    lp.mapCLM 2
      (fun j => ContinuousLinearMap.mul ℝ ℝ (w (S.singularValue j ^ 2) / S.singularValue j))
      hC0
      hmul
  let L :
      H₂ →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    (↑S.leftBasis.repr.toContinuousLinearEquiv :
      K.range.topologicalClosure →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2) ∘L
      K.range.topologicalClosure.orthogonalProjectionOnto
  let R :
      lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] H₁ :=
    K.kerᗮ.subtypeL ∘L
      (↑S.rightBasis.repr.symm.toContinuousLinearEquiv :
        lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] K.kerᗮ)
  let T : H₂ →L[ℝ] H₁ := R ∘L (D ∘L L)
  have hsumT : ∀ g : H₂, HasSum (S.filterSeries w g) (T g) := by
    intro g
    have hsumSubtype :
        HasSum
          (fun j : S.Index ↦
            (D (S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g)) j) •
              (S.rightBasis j : K.kerᗮ))
          (S.rightBasis.repr.symm
            (D (S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g)))) := by
      simpa using
        S.rightBasis.hasSum_repr_symm
          (D (S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g)))
    have hsumH1 := hsumSubtype.mapL K.kerᗮ.subtypeL
    refine HasSum.congr_fun (by simpa [T, R, L] using hsumH1) ?_
    intro j
    have hcoeff :
        S.leftBasis.repr (K.range.topologicalClosure.orthogonalProjectionOnto g) j =
          inner ℝ (S.leftBasis j : H₂) g := by
      rw [HilbertBasis.repr_apply_apply]
      exact K.range.topologicalClosure.inner_orthogonalProjectionOnto_eq_of_mem_left
        (S.leftBasis j) g
    rw [S.filterSeries_apply]
    simp [D, hcoeff]
  have hrec :
      S.reconstructionOperator w ⟨C, hC0, hC⟩ = T := by
    ext g
    calc
      S.reconstructionOperator w ⟨C, hC0, hC⟩ g = ∑' j, S.filterSeries w g j := by
        exact reconstructionOperator_apply S w ⟨C, hC0, hC⟩ g
      _ = T g := (hsumT g).tsum_eq
  rw [hrec]
  intro g
  exact hsumT g

end ContinuousLinearMap.SingularSystem
