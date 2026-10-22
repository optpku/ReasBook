/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open ContinuousLinearMap
open scoped BigOperators InnerProductSpace

noncomputable section

section

variable {ι : Type v} {H : Type u}
variable [Fintype ι] [NormedAddCommGroup H]

/-- Helper for Proposition 4.12: the weighted finite-family Jensen/Cauchy estimate controlling the
squared norm of a sum by the inverse-weighted sum of squared norms. -/
-- Proof step: first bound `‖∑ zᵢ‖` by `∑ ‖zᵢ‖`, then apply the scalar weighted
-- Cauchy-Schwarz inequality to the nonnegative family `‖zᵢ‖`.
private lemma norm_sum_sq_le_weighted_sum_inv
    (α : ι → ℝ) (z : ι → H) (hαpos : ∀ i, 0 < α i) (hαsum : ∑ i, α i = 1) :
    ‖∑ i, z i‖ ^ (2 : ℕ) ≤ ∑ i, (1 / α i) * ‖z i‖ ^ (2 : ℕ) := by
  have hnorm :
      ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := by
    simpa using (norm_sum_le (Finset.univ) z)
  have hsq_norm :
      ‖∑ i, z i‖ ^ (2 : ℕ) ≤ (∑ i, ‖z i‖) ^ (2 : ℕ) := by
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (Finset.sum_nonneg (fun i hi ↦ norm_nonneg (z i)))] using hnorm
  have hscalar :
      (∑ i, ‖z i‖) ^ (2 : ℕ) / ∑ i, α i ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) / α i := by
    simpa using
      (Finset.sq_sum_div_le_sum_sq_div
        Finset.univ (fun i ↦ ‖z i‖) (fun i hi ↦ hαpos i))
  have hweighted :
      (∑ i, ‖z i‖) ^ (2 : ℕ) ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) / α i := by
    simpa [hαsum] using hscalar
  exact hsq_norm.trans <| by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hweighted

end

section

variable {ι : Type v} {H : Type u} {K : ι → Type w}
variable [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The operator obtained by summing the adjoint composites `Lᵢ* ∘ Tᵢ ∘ Lᵢ` over a finite family. -/
def adjointCompositeFamilySum (L : ∀ i, H →L[ℝ] K i) (T : ∀ i, K i → K i) : H → H :=
  fun x ↦ ∑ i, (L i).adjoint (T i (L i x))

/-- Helper for Proposition 4.12: the adjoint satisfies the squared operator-norm estimate needed
to replace `‖Lᵢ* z‖²` by `‖Lᵢ‖² ‖z‖²`. -/
-- Proof step: apply the standard operator norm bound to `A.adjoint`, then square the inequality
-- and rewrite `‖A.adjoint‖ = ‖A‖`.
private lemma adjoint_norm_sq_le_opNorm_sq {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H →L[ℝ] G) (z : G) :
    ‖A.adjoint z‖ ^ (2 : ℕ) ≤ ‖A‖ ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) := by
  have hnorm : ‖A.adjoint z‖ ≤ ‖A‖ * ‖z‖ := by
    simpa using (ContinuousLinearMap.le_opNorm A.adjoint z)
  nlinarith [hnorm, norm_nonneg (A.adjoint z), norm_nonneg A, norm_nonneg z]

/-- Helper for Proposition 4.12: summing the component cocoercivity inequalities yields the lower
bound on the full adjoint composite sum. -/
-- Proof step: move each `Lᵢ` across the inner product by the adjoint identity, apply the
-- cocoercivity of `Tᵢ`, and convert the resulting `‖Tᵢ(Lᵢx) - Tᵢ(Lᵢy)‖²` term into the adjoint
-- expression using the operator norm bound for `Lᵢ*`.
private lemma componentwise_cocoercive_lower_bound
    (L : ∀ i, H →L[ℝ] K i) (βi : ι → ℝ) (T : ∀ i, K i → K i) (hL : ∀ i, L i ≠ 0)
    (hT : ∀ i, CocoerciveOn (βi i) Set.univ (fun x : Set.univ ↦ T i x)) (x y : H) :
    ∑ i,
        (βi i / ‖L i‖ ^ (2 : ℕ)) *
          ‖(L i).adjoint (T i (L i x) - T i (L i y))‖ ^ (2 : ℕ) ≤
      ⟪x - y, adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y⟫_ℝ := by
  have hsummand :
      ∀ i,
        (βi i / ‖L i‖ ^ (2 : ℕ)) *
            ‖(L i).adjoint (T i (L i x) - T i (L i y))‖ ^ (2 : ℕ) ≤
          ⟪x - y, (L i).adjoint (T i (L i x) - T i (L i y))⟫_ℝ := by
    intro i
    let u : K i := T i (L i x) - T i (L i y)
    have hβi_pos : 0 < βi i := (hT i).pos
    have hLi_pos : 0 < ‖L i‖ := norm_pos_iff.mpr (hL i)
    have hLi_sq_pos : 0 < ‖L i‖ ^ (2 : ℕ) := by positivity
    have hnorm_sq :
        ‖(L i).adjoint u‖ ^ (2 : ℕ) ≤ ‖L i‖ ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) :=
      adjoint_norm_sq_le_opNorm_sq (L i) u
    have hscaled :
        (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖(L i).adjoint u‖ ^ (2 : ℕ) ≤
          βi i * ‖u‖ ^ (2 : ℕ) := by
      have hfactor_nonneg : 0 ≤ βi i / ‖L i‖ ^ (2 : ℕ) := by
        exact div_nonneg (le_of_lt hβi_pos) (le_of_lt hLi_sq_pos)
      calc
        (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖(L i).adjoint u‖ ^ (2 : ℕ) ≤
            (βi i / ‖L i‖ ^ (2 : ℕ)) * (‖L i‖ ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hnorm_sq hfactor_nonneg
        _ = βi i * ‖u‖ ^ (2 : ℕ) := by
              field_simp [hLi_sq_pos.ne']
    have hcoco :
        βi i * ‖u‖ ^ (2 : ℕ) ≤ ⟪L i x - L i y, u⟫_ℝ := by
      simpa [u, map_sub] using
        (hT i).ineq ⟨L i x, Set.mem_univ (L i x)⟩ ⟨L i y, Set.mem_univ (L i y)⟩
    have hadjoint :
        ⟪L i x - L i y, u⟫_ℝ = ⟪x - y, (L i).adjoint u⟫_ℝ := by
      calc
        ⟪L i x - L i y, u⟫_ℝ = ⟪L i (x - y), u⟫_ℝ := by rw [map_sub]
        _ = ⟪x - y, (L i).adjoint u⟫_ℝ := by
              simpa using (ContinuousLinearMap.adjoint_inner_right (L i) (x - y) u).symm
    exact hscaled.trans <| hcoco.trans_eq hadjoint
  calc
    ∑ i,
        (βi i / ‖L i‖ ^ (2 : ℕ)) *
          ‖(L i).adjoint (T i (L i x) - T i (L i y))‖ ^ (2 : ℕ)
        ≤ ∑ i, ⟪x - y, (L i).adjoint (T i (L i x) - T i (L i y))⟫_ℝ := by
            exact Finset.sum_le_sum (fun i hi ↦ hsummand i)
    _ = ⟪x - y, ∑ i, (L i).adjoint (T i (L i x) - T i (L i y))⟫_ℝ := by
          rw [inner_sum]
    _ = ⟪x - y, adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y⟫_ℝ := by
          simp [adjointCompositeFamilySum, Finset.sum_sub_distrib, map_sub]

-- Proof sketch: expand the inner product against the finite sum, move each summand across the
-- adjoint, apply the `βᵢ`-cocoercivity hypotheses for the component maps `Tᵢ`, bound the adjoint
-- terms using `‖Lᵢ* z‖ ≤ ‖Lᵢ‖ ‖z‖`, and finish with the weighted Jensen/Cauchy-Schwarz estimate for
-- the coefficient `(∑ i, ‖Lᵢ‖² / βᵢ)⁻¹`.
/-- Proposition 4.12: if each `Tᵢ` is `βᵢ`-cocoercive, then the finite sum
`∑ i, Lᵢ* ∘ Tᵢ ∘ Lᵢ` is `(∑ i, ‖Lᵢ‖² / βᵢ)⁻¹`-cocoercive for a nonempty finite family. -/
theorem cocoerciveOn_univ_adjointCompositeFamilySum
    [Nonempty ι] (L : ∀ i, H →L[ℝ] K i) (βi : ι → ℝ) (T : ∀ i, K i → K i)
    (hL : ∀ i, L i ≠ 0)
    (hT : ∀ i, CocoerciveOn (βi i) Set.univ (fun x : Set.univ ↦ T i x)) :
    CocoerciveOn (1 / ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i) Set.univ
      (fun x : Set.univ ↦ adjointCompositeFamilySum L T x) := by
  classical
  have hβi : ∀ i, 0 < βi i := fun i ↦ (hT i).pos
  let d : ℝ := ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i
  let β : ℝ := 1 / d
  have hd_pos : 0 < d := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hi₀_pos : 0 < ‖L i₀‖ ^ (2 : ℕ) / βi i₀ := by
      have hLi₀_pos : 0 < ‖L i₀‖ := norm_pos_iff.mpr (hL i₀)
      have hLi₀_sq_pos : 0 < ‖L i₀‖ ^ (2 : ℕ) := by positivity
      exact div_pos hLi₀_sq_pos (hβi i₀)
    have hterm_nonneg : ∀ i, 0 ≤ ‖L i‖ ^ (2 : ℕ) / βi i := by
      intro i
      have hLi_sq_nonneg : 0 ≤ ‖L i‖ ^ (2 : ℕ) := by positivity
      exact div_nonneg hLi_sq_nonneg (le_of_lt (hβi i))
    have hi₀_le : ‖L i₀‖ ^ (2 : ℕ) / βi i₀ ≤ ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i := by
      simpa using
        (Finset.single_le_sum
          (fun j hj ↦ hterm_nonneg j)
          (show i₀ ∈ (Finset.univ : Finset ι) by simp))
    simpa [d] using lt_of_lt_of_le hi₀_pos hi₀_le
  have hβ_pos : 0 < β := by
    simpa [β] using inv_pos.mpr hd_pos
  refine ⟨by simpa [β, d] using hβ_pos, ?_⟩
  intro x y
  let α : ι → ℝ := fun i ↦ β * ‖L i‖ ^ (2 : ℕ) / βi i
  let z : ι → H := fun i ↦ (L i).adjoint (T i (L i x) - T i (L i y))
  have hαpos : ∀ i, 0 < α i := by
    intro i
    have hLi_pos : 0 < ‖L i‖ := norm_pos_iff.mpr (hL i)
    have hLi_sq_pos : 0 < ‖L i‖ ^ (2 : ℕ) := by positivity
    dsimp [α]
    exact div_pos (mul_pos hβ_pos hLi_sq_pos) (hβi i)
  have hαsum : ∑ i, α i = 1 := by
    -- The normalization matches the textbook coefficients `αᵢ = β ‖Lᵢ‖² / βᵢ`.
    calc
      ∑ i, α i = β * ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i := by
        simp [α, Finset.mul_sum, mul_assoc, mul_comm, div_eq_mul_inv]
      _ = 1 := by
        have hd_ne : d ≠ 0 := hd_pos.ne'
        simp [β, d, hd_ne]
  have hzsum :
      ∑ i, z i = adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y := by
    -- The adjoint composite sum difference is the sum of the component differences.
    simp [adjointCompositeFamilySum, z, Finset.sum_sub_distrib, map_sub]
  have hcoef :
      ∀ i, β * (1 / α i) = βi i / ‖L i‖ ^ (2 : ℕ) := by
    intro i
    have hLi_pos : 0 < ‖L i‖ := norm_pos_iff.mpr (hL i)
    have hLi_sq_pos : 0 < ‖L i‖ ^ (2 : ℕ) := by positivity
    have hαi_pos : 0 < α i := hαpos i
    dsimp [α]
    field_simp [hαi_pos.ne', hβ_pos.ne', hLi_sq_pos.ne', (hβi i).ne']
  have hweighted :
      β * ‖adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y‖ ^ (2 : ℕ) ≤
        ∑ i, (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖z i‖ ^ (2 : ℕ) := by
    have hnorm :
        ‖∑ i, z i‖ ^ (2 : ℕ) ≤ ∑ i, (1 / α i) * ‖z i‖ ^ (2 : ℕ) :=
      norm_sum_sq_le_weighted_sum_inv α z hαpos hαsum
    have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
    calc
      β * ‖adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y‖ ^ (2 : ℕ)
          = β * ‖∑ i, z i‖ ^ (2 : ℕ) := by rw [← hzsum]
      _ ≤ β * ∑ i, (1 / α i) * ‖z i‖ ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hnorm hβ_nonneg
      _ = ∑ i, (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖z i‖ ^ (2 : ℕ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              β * ((1 / α i) * ‖z i‖ ^ (2 : ℕ))
                  = (β * (1 / α i)) * ‖z i‖ ^ (2 : ℕ) := by ring
              _ = (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖z i‖ ^ (2 : ℕ) := by
                    rw [hcoef i]
  -- Route correction: finish with the weighted scalar Cauchy step, not by ad hoc expansion of
  -- the full squared norm of the operator sum.
  exact hweighted.trans <|
    componentwise_cocoercive_lower_bound L βi T hL hT x y

end
