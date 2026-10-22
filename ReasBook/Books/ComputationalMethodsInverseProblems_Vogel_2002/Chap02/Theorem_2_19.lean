/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_18
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_17.Pseudoinverse
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_19.Reconstruction

public section

noncomputable section

open Filter
open scoped Topology BigOperators ENNReal

namespace ContinuousLinearMap.SingularSystem

universe u v w

variable {H₁ : Type u} {H₂ : Type v} {ι : Type w}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable {K : H₁ →L[ℝ] H₂}

/-- Theorem 2.19 (1). If each scalar filter `w α` satisfies the uniform inverse bound
`∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C`, then the reconstruction family from `(2.24)` is a
linear regularization scheme in the sense of Definition 2.18. -/
theorem reconstructionOperator_isLinear
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C) :
    FilterRegularization.IsLinear ℝ (fun α g ↦ S.reconstructionFamily w h_bound α g) := by
  -- Use the bundled reconstruction family as the continuous-linear-map witness.
  simpa using
    FilterRegularization.IsLinear.ofContinuousLinearMapFamily
      (S.reconstructionFamily w h_bound)

/-- Helper for Theorem 2.19: the `u_j` coefficient of `K f` is the singular value times the
corresponding `v_j` coefficient of `f`. -/
theorem inner_leftBasis_map_eq_singularValue_mul_inner_rightBasis
    (S : SingularSystem K) (f : H₁) (j : S.Index) :
    inner ℝ (S.leftBasis j : H₂) (K f) =
      S.singularValue j * inner ℝ (S.rightBasis j : H₁) f := by
  -- Move `K` across the inner product and then apply the singular-system axiom.
  rw [← ContinuousLinearMap.adjoint_inner_left K f (S.leftBasis j : H₂),
    S.adjoint_map_left j, inner_smul_left]
  simp

omit [CompleteSpace H₂] in
/-- Helper for Theorem 2.19: the range-restricted pseudoinverse reconstructs every datum already
in `K.range`. -/
theorem map_partialPseudoInverseOnRange
    (g : K.range) :
    K (K.kerOrthogonalEquivRange.symm g : H₁) = (g : H₂) := by
  -- Evaluate the inverse equivalence and then forget back to `H₂`.
  simpa using
    congrArg (fun y : K.range ↦ (y : H₂)) (K.kerOrthogonalEquivRange_symm_apply g)

/-- Helper for Theorem 2.19: the right-basis coordinates of
`K.kerOrthogonalEquivRange.symm g` are the singular-value-rescaled left-basis coefficients of
`g`. -/
theorem partialPseudoInverseOnRange_repr
    (S : SingularSystem K) (g : K.range) (j : S.Index) :
    S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j =
      inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j := by
  have hs_ne : S.singularValue j ≠ 0 := ne_of_gt (S.singularValue_pos j)
  have hmap :
      K (((K.kerOrthogonalEquivRange.symm g : K.kerᗮ) : H₁)) = (g : H₂) := by
    -- Applying `K` to the inverse image recovers the original range datum.
    simpa using map_partialPseudoInverseOnRange g
  have hcoeff :
      inner ℝ (S.leftBasis j : H₂) (g : H₂) =
        S.singularValue j *
          inner ℝ (S.rightBasis j : H₁) ((K.kerOrthogonalEquivRange.symm g : K.kerᗮ) : H₁) := by
    -- Rewrite the left-basis coefficient through the singular-system relation on the inverse image.
    simpa [hmap] using
      inner_leftBasis_map_eq_singularValue_mul_inner_rightBasis
        S (((K.kerOrthogonalEquivRange.symm g : K.kerᗮ) : H₁)) j
  -- Solve for the right-basis coefficient by dividing through the positive singular value.
  rw [HilbertBasis.repr_apply_apply]
  apply (eq_div_iff hs_ne).2
  simpa [mul_comm] using hcoeff.symm

/-- Helper for Theorem 2.19: each reconstruction operator satisfies the standard operator-norm
perturbation estimate from `(2.25)`. -/
theorem reconstructionFamily_apply_sub_le
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (g₁ g₂ : H₂) :
    ‖S.reconstructionFamily w h_bound α g₁ - S.reconstructionFamily w h_bound α g₂‖ ≤
      ‖S.reconstructionFamily w h_bound α‖ * ‖g₁ - g₂‖ := by
  -- This is the standard operator-norm estimate for the bundled reconstruction operator.
  simpa [ContinuousLinearMap.map_sub] using
    (S.reconstructionFamily w h_bound α).le_opNorm (g₁ - g₂)

/-- Helper for Theorem 2.19: the singular-system series for
`(K.kerOrthogonalEquivRange.symm g : H₁)` converges in `H₁`. -/
theorem hasSum_partialPseudoInverseOnRange
    (S : SingularSystem K) (g : K.range) :
    HasSum
      (fun j : S.Index ↦
        ((inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j) •
          (S.rightBasis j : H₁)))
      (K.kerOrthogonalEquivRange.symm g : H₁) := by
  have hsum :
      HasSum
        (fun j : S.Index ↦
          (S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j •
            (S.rightBasis j : K.kerᗮ)))
        (K.kerOrthogonalEquivRange.symm g) := by
    -- Expand the inverse image in the right Hilbert basis of `K.kerᗮ`.
    simpa using
      (S.rightBasis.hasSum_repr (K.kerOrthogonalEquivRange.symm g))
  have hsumH₁ :
      HasSum
        (fun j : S.Index ↦
          (S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j •
            (S.rightBasis j : H₁)))
        (K.kerOrthogonalEquivRange.symm g : H₁) := by
    -- Forget the subtype codomain to view the same series in `H₁`.
    simpa using hsum.mapL K.kerᗮ.subtypeL
  -- Rewrite the coefficients through the left-basis formula for the inverse image.
  refine HasSum.congr_fun hsumH₁ ?_
  intro j
  rw [partialPseudoInverseOnRange_repr S g j]

/-- Helper for Theorem 2.19: the exact-data reconstruction error is the right-basis expansion
obtained by multiplying the pseudoinverse coordinates by the bias multipliers. -/
theorem exactDataError_hasSum
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) :
    HasSum
      (fun j : S.Index ↦
        (((w α (S.singularValue j ^ 2) - 1) *
            S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j) •
          (S.rightBasis j : H₁)))
      (S.reconstructionFamily w h_bound α (g : H₂) -
        (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  have hrec :
      HasSum
        (fun j : S.Index ↦
          (((w α (S.singularValue j ^ 2) / S.singularValue j) *
              inner ℝ (S.leftBasis j : H₂) (g : H₂)) •
            (S.rightBasis j : H₁)))
        (S.reconstructionFamily w h_bound α (g : H₂)) := by
    -- Rewrite the reconstruction family through its filter-series owner theorem.
    change HasSum (S.filterSeries (w α) (g : H₂))
      (S.reconstructionFamily w h_bound α (g : H₂))
    simpa [reconstructionFamily_apply] using
      (S.hasFilterRepresentation_reconstructionOperator (w α) (h_bound α)).hasSum (g : H₂)
  have hpinv := hasSum_partialPseudoInverseOnRange S g
  have hsub := hrec.sub hpinv
  refine HasSum.congr_fun hsub ?_
  intro j
  rw [partialPseudoInverseOnRange_repr S g j]
  have hs_ne : S.singularValue j ≠ 0 := ne_of_gt (S.singularValue_pos j)
  rw [← sub_smul]
  congr 1
  -- Clear the single denominator to identify the bias multiplier.
  field_simp [hs_ne]

/-- Helper for Theorem 2.19: a uniform bound on the bias multipliers controls the exact-data
reconstruction error by the norm of `(K.kerOrthogonalEquivRange.symm g : H₁)`. -/
theorem exactDataError_le_uniformBias
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j : S.Index, |w α (S.singularValue j ^ 2) - 1| ≤ B) :
    ‖S.reconstructionFamily w h_bound α (g : H₂) -
        (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
      B * ‖(K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
  let pinv : H₁ := (K.kerOrthogonalEquivRange.symm g : H₁)
  change ‖S.reconstructionFamily w h_bound α (g : H₂) - pinv‖ ≤ B * ‖pinv‖
  let c : lp (fun _ : S.Index ↦ ℝ) 2 :=
    S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g)
  have hmul :
      ∀ j : S.Index,
        ‖ContinuousLinearMap.mul ℝ ℝ (w α (S.singularValue j ^ 2) - 1)‖ ≤ B := by
    intro j
    rw [ContinuousLinearMap.opNorm_mul_apply]
    simpa [Real.norm_eq_abs] using hB j
  let D : lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    lp.mapCLM 2
      (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (w α (S.singularValue j ^ 2) - 1))
      hB0
      hmul
  let e := S.rightBasis.repr
  let y : K.kerᗮ := e.symm (D c)
  have hdiagSubtype :
      HasSum
        (fun j : S.Index ↦
          (D c j) • (S.rightBasis j : K.kerᗮ))
        y := by
    -- Expand the diagonal multiplier output in the right Hilbert basis.
    simpa [c, e, y] using S.rightBasis.hasSum_repr_symm (D c)
  have hdiag :
      HasSum
        (fun j : S.Index ↦
          (((w α (S.singularValue j ^ 2) - 1) *
              S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j) •
            (S.rightBasis j : H₁)))
        ((y : K.kerᗮ) : H₁) := by
    -- Forget the subtype codomain and unfold the diagonal multiplier coordinatewise.
    refine HasSum.congr_fun (by simpa [D, c] using hdiagSubtype.mapL K.kerᗮ.subtypeL) ?_
    intro j
    apply congrArg (fun a : ℝ ↦ a • (S.rightBasis j : H₁))
    ring
  have herr :
      S.reconstructionFamily w h_bound α (g : H₂) - pinv =
        ((y : K.kerᗮ) : H₁) := by
    -- The exact-data error is the same right-basis series as the diagonal multiplier output.
    exact (exactDataError_hasSum S w h_bound g α).unique hdiag
  have hDnorm : ‖D‖ ≤ B := by
    -- The diagonal operator inherits the uniform multiplier bound.
    exact lp.norm_mapCLM_le 2
      (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (w α (S.singularValue j ^ 2) - 1))
      hB0
      hmul
  have hc :
      ‖c‖ = ‖pinv‖ := by
    -- `c` is the right-basis coefficient vector of the range pseudoinverse.
    calc
      ‖c‖ = ‖K.kerOrthogonalEquivRange.symm g‖ := by
        simp [c]
      _ = ‖pinv‖ := by
        rfl
  calc
    ‖S.reconstructionFamily w h_bound α (g : H₂) - pinv‖ =
        ‖((y : K.kerᗮ) : H₁)‖ := by
          rw [herr]
    _ = ‖y‖ := by
          rfl
    _ = ‖D c‖ := by
          simp [y]
    _ ≤ ‖D‖ * ‖c‖ := by
          exact D.le_opNorm c
    _ ≤ B * ‖c‖ := by
          exact mul_le_mul_of_nonneg_right hDnorm (norm_nonneg c)
    _ = B * ‖pinv‖ := by
          rw [hc]

/-- Helper for Theorem 2.19: finite singular heads approximate both
`(K.kerOrthogonalEquivRange.symm g : H₁)` and the corresponding exact datum `g`. -/
theorem rangePseudoInverseFiniteHeadApprox
    (S : SingularSystem K) (g : K.range) {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset S.Index,
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
          Finset.sum F
            (fun j ↦
              ((inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j) •
                (S.rightBasis j : H₁)))‖ ≤ η ∧
        ‖(g : H₂) -
            K (Finset.sum F
              (fun j ↦
                ((inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j) •
                  (S.rightBasis j : H₁))))‖ ≤ η := by
  let pinv : H₁ := (K.kerOrthogonalEquivRange.symm g : H₁)
  let f : S.Index → H₁ := fun j ↦
    ((inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j) •
      (S.rightBasis j : H₁))
  have hsum : HasSum f pinv := by
    simpa [pinv] using hasSum_partialPseudoInverseOnRange S g
  have hmap_pinv : K pinv = (g : H₂) := by
    simpa [pinv] using map_partialPseudoInverseOnRange g
  have hsumMap : HasSum (fun j : S.Index ↦ K (f j)) (g : H₂) := by
    -- Map the same partial sums through `K` to approximate the original range datum.
    simpa [f, hmap_pinv] using hsum.mapL K
  have hH1 :
      ∀ᶠ F : Finset S.Index in Filter.atTop,
        ‖Finset.sum F f - pinv‖ < η := by
    -- The partial sums of the pseudoinverse series converge to the canonical inverse image.
    filter_upwards [hsum.eventually (Metric.ball_mem_nhds pinv hη)] with F hF
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hF
  have hH2 :
      ∀ᶠ F : Finset S.Index in Filter.atTop,
        ‖Finset.sum F (fun j ↦ K (f j)) - (g : H₂)‖ < η := by
    -- The mapped partial sums converge to `g`.
    filter_upwards [hsumMap.eventually (Metric.ball_mem_nhds (g : H₂) hη)] with F hF
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hF
  rcases Filter.mem_atTop_sets.1 (hH1.and hH2) with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  specialize hF F le_rfl
  rcases hF with ⟨hF1, hF2⟩
  constructor
  · change ‖pinv - Finset.sum F f‖ ≤ η
    have hF1' := hF1.le
    rwa [norm_sub_rev] at hF1'
  · change ‖(g : H₂) - K (Finset.sum F f)‖ ≤ η
    simpa [f, map_sum, norm_sub_rev] using hF2.le

/-- Helper for Theorem 2.19: finite singular-head approximations can be kept inside `K.kerᗮ`
with explicit finite support in the right basis. -/
theorem rangePseudoInverseFiniteHeadApproxInKerOrthogonal
    (S : SingularSystem K) (g : K.range) {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset S.Index, ∃ xF : K.kerᗮ,
      (∀ j ∉ F, S.rightBasis.repr xF j = 0) ∧
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xF : H₁)‖ ≤ η ∧
      ‖(g : H₂) - K (xF : H₁)‖ ≤ η := by
  let horth := S.rightBasis.orthonormal
  rcases rangePseudoInverseFiniteHeadApprox S g hη with
    ⟨F, happrox, hdata⟩
  let coeff : S.Index → ℝ := fun j ↦
    inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j
  let xF : K.kerᗮ :=
    Finset.sum F fun j ↦ coeff j • (S.rightBasis j : K.kerᗮ)
  have hxF :
      ((xF : K.kerᗮ) : H₁) =
        Finset.sum F fun j ↦ coeff j • (S.rightBasis j : H₁) := by
    -- Forgetting the subtype turns the finite `K.kerᗮ` head into the ambient finite singular head.
    simp [xF, coeff]
  refine ⟨F, xF, ?_, ?_, ?_⟩
  · intro j hj
    -- Coordinates outside the chosen finite head vanish because only basis vectors from `F` appear.
    rw [HilbertBasis.repr_apply_apply, inner_sum]
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hkj : j ≠ k := by
      intro hkj
      apply hj
      simpa [hkj] using hk
    rw [inner_smul_right]
    simp [horth.inner_eq_zero hkj]
  · -- Rewrite the ambient approximation statement through the subtype-packaged finite head.
    simpa [hxF.symm, coeff] using happrox
  · -- The mapped finite head is the same ambient sum viewed through `K`.
    simpa [hxF.symm, coeff] using hdata

omit [CompleteSpace H₂] in
/-- Helper for Theorem 2.19: `(K.kerOrthogonalEquivRange.symm · : H₁)` inverts `K` on `K.kerᗮ`. -/
theorem rangePseudoInverse_apply_map_kerOrthogonal
    (x : K.kerᗮ) :
    (K.kerOrthogonalEquivRange.symm ⟨K (x : H₁), by exact ⟨(x : H₁), rfl⟩⟩ : H₁) = (x : H₁) := by
  have hx :
      K.kerOrthogonalEquivRange x =
        ⟨K (x : H₁), by exact ⟨(x : H₁), rfl⟩⟩ := by
    -- Both points of `K.range` are obtained by applying `K` to the same `K.kerᗮ` vector.
    ext
    simp [ContinuousLinearMap.kerOrthogonalEquivRange_apply]
  have hsymm :
      K.kerOrthogonalEquivRange.symm
          ⟨K (x : H₁), by exact ⟨(x : H₁), rfl⟩⟩ = x := by
    -- Apply the inverse equivalence to the range identity from the previous step.
    simpa using (congrArg K.kerOrthogonalEquivRange.symm hx).symm
  -- Forget the subtype after identifying the inverse image in `K.kerᗮ`.
  simpa using congrArg (fun z : K.kerᗮ ↦ (z : H₁)) hsymm

/-- Helper for Theorem 2.19: a finite right-basis head only depends on the filter bias on its
own support. -/
theorem finiteHeadReconstructionError_le
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (F : Finset S.Index) (xF : K.kerᗮ)
    (hsupport : ∀ j : S.Index, j ∉ F → S.rightBasis.repr xF j = 0)
    (B : ℝ)
    (hB : ∀ j ∈ F, |w α (S.singularValue j ^ 2) - 1| ≤ B) :
    ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖ ≤
      B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) := by
  let gF : K.range := ⟨K (xF : H₁), by exact ⟨(xF : H₁), rfl⟩⟩
  let e : S.Index → H₁ := fun j ↦
    (((w α (S.singularValue j ^ 2) - 1) * S.rightBasis.repr xF j) •
      (S.rightBasis j : H₁))
  have hsymm :
      K.kerOrthogonalEquivRange.symm gF = xF := by
    -- The inverse image of the range point `K xF` is exactly the chosen `K.kerᗮ` head.
    have hx :
        K.kerOrthogonalEquivRange xF = gF := by
      ext
      simp [gF, ContinuousLinearMap.kerOrthogonalEquivRange_apply]
    simpa [gF] using (congrArg K.kerOrthogonalEquivRange.symm hx).symm
  have herrSeries :
      HasSum e (S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)) := by
    -- Rewrite the exact-data error for the range datum `K xF`.
    simpa [e, gF, hsymm, rangePseudoInverse_apply_map_kerOrthogonal xF] using
      exactDataError_hasSum S w h_bound gF α
  have hsumFinite : HasSum e (Finset.sum F e) := by
    -- The error series is finite because the right-basis coordinates vanish off `F`.
    refine hasSum_sum_of_ne_finset_zero ?_
    intro j hj
    simp [e, hsupport j hj]
  have herr :
      S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁) =
        Finset.sum F e := by
    -- Identify the exact-data error with the finite supported sum.
    exact herrSeries.unique hsumFinite
  calc
    ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖ = ‖Finset.sum F e‖ := by
      rw [herr]
    _ ≤ Finset.sum F fun j ↦ ‖e j‖ := norm_sum_le _ _
    _ = Finset.sum F fun j ↦ |w α (S.singularValue j ^ 2) - 1| * |S.rightBasis.repr xF j| := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have horth := S.rightBasis.orthonormal
      have hbasis : ‖(S.rightBasis j : H₁)‖ = 1 := by
        simpa using horth.norm_eq_one j
      calc
        ‖((w α (S.singularValue j ^ 2) - 1) * S.rightBasis.repr xF j) •
            (S.rightBasis j : H₁)‖ =
            |(w α (S.singularValue j ^ 2) - 1) * S.rightBasis.repr xF j| *
              ‖(S.rightBasis j : H₁)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = |w α (S.singularValue j ^ 2) - 1| * |S.rightBasis.repr xF j| * 1 := by
              rw [abs_mul, hbasis]
        _ = |w α (S.singularValue j ^ 2) - 1| * |S.rightBasis.repr xF j| := by ring
    _ ≤ Finset.sum F fun j ↦ B * |S.rightBasis.repr xF j| := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact mul_le_mul_of_nonneg_right (hB j hj) (abs_nonneg _)
    _ = B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) := by
      rw [Finset.mul_sum]

/-- Helper for Theorem 2.19: a finite right-basis head is controlled in norm by the largest bias
multiplier on its support. -/
theorem finiteHeadReconstructionError_le_norm
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (F : Finset S.Index) (xF : K.kerᗮ)
    (hsupport : ∀ j : S.Index, j ∉ F → S.rightBasis.repr xF j = 0)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j ∈ F, |w α (S.singularValue j ^ 2) - 1| ≤ B) :
    ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖ ≤
      B * ‖(xF : H₁)‖ := by
  let gF : K.range := ⟨K (xF : H₁), by exact ⟨(xF : H₁), rfl⟩⟩
  let c : lp (fun _ : S.Index ↦ ℝ) 2 := S.rightBasis.repr xF
  let m : S.Index → ℝ := fun j ↦ if j ∈ F then w α (S.singularValue j ^ 2) - 1 else 0
  have hmul :
      ∀ j : S.Index, ‖ContinuousLinearMap.mul ℝ ℝ (m j)‖ ≤ B := by
    intro j
    rw [ContinuousLinearMap.opNorm_mul_apply]
    by_cases hj : j ∈ F
    · -- On the chosen support, the multiplier is bounded by the prescribed bias budget.
      simpa [m, hj, Real.norm_eq_abs] using hB j hj
    · -- Off the support, the auxiliary multiplier vanishes.
      simp [m, hj, hB0]
  let D : lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    lp.mapCLM 2 (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (m j)) hB0 hmul
  let e := S.rightBasis.repr
  let y : K.kerᗮ := e.symm (D c)
  have hdiagSubtype :
      HasSum
        (fun j : S.Index ↦
          (D c j) • (S.rightBasis j : K.kerᗮ))
        y := by
    -- Expand the diagonal output in the right Hilbert basis.
    simpa [c, e, y] using S.rightBasis.hasSum_repr_symm (D c)
  have hdiag :
      HasSum
        (fun j : S.Index ↦
          (((w α (S.singularValue j ^ 2) - 1) * S.rightBasis.repr xF j) •
            (S.rightBasis j : H₁)))
        ((y : K.kerᗮ) : H₁) := by
    -- Route correction: encode the finite-support bias multiplier as a bounded diagonal map on
    -- `lp 2`, so the head estimate depends on `‖xF‖` rather than an `l1` support sum.
    refine HasSum.congr_fun (by simpa [D, c] using hdiagSubtype.mapL K.kerᗮ.subtypeL) ?_
    intro j
    have hm :
        m j * S.rightBasis.repr xF j =
          (w α (S.singularValue j ^ 2) - 1) * S.rightBasis.repr xF j := by
      by_cases hj : j ∈ F
      · simp [m, hj]
      · simp [m, hj, hsupport j hj]
    -- Rewrite the diagonal coefficient to the actual bias multiplier on `xF`.
    simpa using congrArg (fun a : ℝ ↦ a • (S.rightBasis j : H₁)) hm.symm
  have hsymm :
      K.kerOrthogonalEquivRange.symm gF = xF := by
    -- The inverse image of the range datum `K xF` is the chosen head itself.
    have hx :
        K.kerOrthogonalEquivRange xF = gF := by
      ext
      simp [gF, ContinuousLinearMap.kerOrthogonalEquivRange_apply]
    simpa [gF] using (congrArg K.kerOrthogonalEquivRange.symm hx).symm
  have hdiagRange :
      HasSum
        (fun j : S.Index ↦
          (((w α (S.singularValue j ^ 2) - 1) *
              S.rightBasis.repr (K.kerOrthogonalEquivRange.symm gF) j) •
            (S.rightBasis j : H₁)))
        ((y : K.kerᗮ) : H₁) := by
    -- Identify the supported head with the canonical inverse image of `gF`.
    simpa [hsymm] using hdiag
  have herr :
      S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁) =
        ((y : K.kerᗮ) : H₁) := by
    -- The exact-data error equals the diagonal multiplier output on the supported head.
    simpa [gF, hsymm, rangePseudoInverse_apply_map_kerOrthogonal xF] using
      (exactDataError_hasSum S w h_bound gF α).unique hdiagRange
  have hDnorm : ‖D‖ ≤ B := by
    -- The auxiliary diagonal map inherits the supportwise bias bound.
    exact lp.norm_mapCLM_le 2 (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (m j)) hB0 hmul
  have hc :
      ‖c‖ = ‖(xF : H₁)‖ := by
    -- `c` is the right-basis coordinate vector of `xF`.
    calc
      ‖c‖ = ‖xF‖ := by
        simp [c]
      _ = ‖(xF : H₁)‖ := by
        rfl
  calc
    ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖ =
        ‖((y : K.kerᗮ) : H₁)‖ := by
          rw [herr]
    _ = ‖y‖ := by
          rfl
    _ = ‖D c‖ := by
          simp [y]
    _ ≤ ‖D‖ * ‖c‖ := by
          exact D.le_opNorm c
    _ ≤ B * ‖c‖ := by
          exact mul_le_mul_of_nonneg_right hDnorm (norm_nonneg c)
    _ = B * ‖(xF : H₁)‖ := by
          rw [hc]

/-- Helper for Theorem 2.19: split the exact-data reconstruction error against a finite
right-basis head and bound the three resulting pieces separately. -/
theorem exactDataErrorBoundFromFiniteHead
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) (F : Finset S.Index) (xF : K.kerᗮ)
    (hsupport : ∀ j : S.Index, j ∉ F → S.rightBasis.repr xF j = 0)
    (B : ℝ) (_hB0 : 0 ≤ B)
    (hB : ∀ j ∈ F, |w α (S.singularValue j ^ 2) - 1| ≤ B) :
    ‖S.reconstructionFamily w h_bound α (g : H₂) -
        (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
      ‖S.reconstructionFamily w h_bound α‖ * ‖(g : H₂) - K (xF : H₁)‖ +
        B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) +
          ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xF : H₁)‖ := by
  let Rα := S.reconstructionFamily w h_bound α
  let pinv : H₁ := (K.kerOrthogonalEquivRange.symm g : H₁)
  have hsplit :
      Rα (g : H₂) - pinv =
        (Rα (g : H₂) - Rα (K (xF : H₁))) +
          ((Rα (K (xF : H₁)) - (xF : H₁)) + ((xF : H₁) - pinv)) := by
    -- Split the reconstruction error into transport, finite-head, and approximation terms.
    simp [Rα, pinv, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have htail :
      ‖Rα (g : H₂) - Rα (K (xF : H₁))‖ ≤
        ‖Rα‖ * ‖(g : H₂) - K (xF : H₁)‖ := by
    -- The transport term is controlled by the operator norm of the chosen reconstruction map.
    simpa [Rα] using
      reconstructionFamily_apply_sub_le
        S w h_bound α (g : H₂) (K (xF : H₁))
  have hhead :
      ‖Rα (K (xF : H₁)) - (xF : H₁)‖ ≤
        B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) := by
    -- The finite-head exact-data error only depends on the bias on the active support.
    simpa [Rα] using
      finiteHeadReconstructionError_le
        S w h_bound α F xF hsupport B hB
  have happrox :
      ‖(xF : H₁) - pinv‖ = ‖pinv - (xF : H₁)‖ := by
    -- Rewrite the approximation term to match the target orientation.
    rw [norm_sub_rev]
  calc
    ‖S.reconstructionFamily w h_bound α (g : H₂) - pinv‖ = ‖Rα (g : H₂) - pinv‖ := by
      rfl
    _ = ‖(Rα (g : H₂) - Rα (K (xF : H₁))) +
          ((Rα (K (xF : H₁)) - (xF : H₁)) + ((xF : H₁) - pinv))‖ := by
      rw [hsplit]
    _ ≤ ‖Rα (g : H₂) - Rα (K (xF : H₁))‖ +
          ‖(Rα (K (xF : H₁)) - (xF : H₁)) + ((xF : H₁) - pinv)‖ := by
      exact norm_add_le _ _
    _ ≤ ‖Rα (g : H₂) - Rα (K (xF : H₁))‖ +
          (‖Rα (K (xF : H₁)) - (xF : H₁)‖ + ‖(xF : H₁) - pinv‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖Rα‖ * ‖(g : H₂) - K (xF : H₁)‖ +
          (B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) + ‖(xF : H₁) - pinv‖) := by
      exact add_le_add htail (add_le_add hhead le_rfl)
    _ = ‖Rα‖ * ‖(g : H₂) - K (xF : H₁)‖ +
          B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) +
            ‖pinv - (xF : H₁)‖ := by
      rw [happrox]
      ring

/-- Helper for Theorem 2.19: once a finite head already meets the approximation, transport, and
supportwise bias budgets at one stage, the three stagewise exact-data inequalities follow
immediately. -/
theorem exactDataStageFromFiniteHeadBudget
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) {δ ηApprox ηTail ηHead : ℝ}
    (F : Finset S.Index) (xF : K.kerᗮ)
    (hsupport : ∀ j : S.Index, j ∉ F → S.rightBasis.repr xF j = 0)
    (B : ℝ)
    (happrox :
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xF : H₁)‖ ≤ ηApprox)
    (hdata : ‖(g : H₂) - K (xF : H₁)‖ ≤ δ)
    (hB : ∀ j ∈ F, |w α (S.singularValue j ^ 2) - 1| ≤ B)
    (hheadBudget :
      B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) ≤ ηHead)
    (hnorm :
      ‖S.reconstructionFamily w h_bound α‖ * δ ≤ ηTail) :
    ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xF : H₁)‖ ≤ ηApprox ∧
      ‖S.reconstructionFamily w h_bound α (g : H₂) -
          S.reconstructionFamily w h_bound α (K (xF : H₁))‖ ≤ ηTail ∧
      ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖ ≤ ηHead := by
  refine ⟨happrox, ?_, ?_⟩
  · -- The data-tail term is controlled by the operator norm and the chosen stage radius.
    calc
      ‖S.reconstructionFamily w h_bound α (g : H₂) -
          S.reconstructionFamily w h_bound α (K (xF : H₁))‖
          ≤ ‖S.reconstructionFamily w h_bound α‖ * ‖(g : H₂) - K (xF : H₁)‖ := by
            simpa using
              reconstructionFamily_apply_sub_le
                S w h_bound α (g : H₂) (K (xF : H₁))
      _ ≤ ‖S.reconstructionFamily w h_bound α‖ * δ := by
            exact mul_le_mul_of_nonneg_left hdata (norm_nonneg _)
      _ ≤ ηTail := hnorm
  · -- The exact-data head term depends only on the bias multipliers over the active support.
    calc
      ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖
          ≤ B * (Finset.sum F fun j ↦ |S.rightBasis.repr xF j|) := by
            simpa using
              finiteHeadReconstructionError_le
                S w h_bound α F xF hsupport B hB
      _ ≤ ηHead := hheadBudget

/-- Helper for Theorem 2.19: the one-stage exact-data bounds also follow from the norm-based
finite-head estimate `finiteHeadReconstructionError_le_norm`. -/
theorem exactDataStageFromFiniteHeadBudgetNorm
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) {δ ηApprox ηTail ηHead : ℝ}
    (F : Finset S.Index) (xF : K.kerᗮ)
    (hsupport : ∀ j : S.Index, j ∉ F → S.rightBasis.repr xF j = 0)
    (B : ℝ) (hB0 : 0 ≤ B)
    (happrox :
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xF : H₁)‖ ≤ ηApprox)
    (hdata : ‖(g : H₂) - K (xF : H₁)‖ ≤ δ)
    (hB : ∀ j ∈ F, |w α (S.singularValue j ^ 2) - 1| ≤ B)
    (hheadBudget : B * ‖(xF : H₁)‖ ≤ ηHead)
    (hnorm :
      ‖S.reconstructionFamily w h_bound α‖ * δ ≤ ηTail) :
    ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xF : H₁)‖ ≤ ηApprox ∧
      ‖S.reconstructionFamily w h_bound α (g : H₂) -
          S.reconstructionFamily w h_bound α (K (xF : H₁))‖ ≤ ηTail ∧
      ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖ ≤ ηHead := by
  refine ⟨happrox, ?_, ?_⟩
  · -- The data-tail term is again controlled by the operator norm and the chosen radius `δ`.
    calc
      ‖S.reconstructionFamily w h_bound α (g : H₂) -
          S.reconstructionFamily w h_bound α (K (xF : H₁))‖
          ≤ ‖S.reconstructionFamily w h_bound α‖ * ‖(g : H₂) - K (xF : H₁)‖ := by
            simpa using
              reconstructionFamily_apply_sub_le
                S w h_bound α (g : H₂) (K (xF : H₁))
      _ ≤ ‖S.reconstructionFamily w h_bound α‖ * δ := by
            exact mul_le_mul_of_nonneg_left hdata (norm_nonneg _)
      _ ≤ ηTail := hnorm
  · -- The head term now closes through the `l2`-norm estimate for the supported finite head.
    calc
      ‖S.reconstructionFamily w h_bound α (K (xF : H₁)) - (xF : H₁)‖
          ≤ B * ‖(xF : H₁)‖ := by
            simpa using
              finiteHeadReconstructionError_le_norm
                S w h_bound α F xF hsupport B hB0 hB
      _ ≤ ηHead := hheadBudget

/-- Helper for Theorem 2.19: for a fixed operator scale, one can choose a finite right-basis head
whose approximation error and exact-data tail error are both smaller than the normalized scale. -/
theorem finiteHeadApproxForChosenOperatorScale
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset S.Index, ∃ xF : K.kerᗮ,
      (∀ j ∉ F, S.rightBasis.repr xF j = 0) ∧
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xF : H₁)‖ ≤
        ε / (2 * (‖S.reconstructionFamily w h_bound α‖ + 1)) ∧
      ‖(g : H₂) - K (xF : H₁)‖ ≤
        ε / (2 * (‖S.reconstructionFamily w h_bound α‖ + 1)) := by
  have hden : 0 < 2 * (‖S.reconstructionFamily w h_bound α‖ + 1) := by
    -- The normalization scale is strictly positive because the operator norm is nonnegative.
    positivity
  have hη :
      0 < ε / (2 * (‖S.reconstructionFamily w h_bound α‖ + 1)) := by
    -- Dividing the positive tolerance by the positive normalization scale keeps it positive.
    exact div_pos hε hden
  -- Choose a finite singular head with both ambient and data errors below the normalized scale.
  exact
    rangePseudoInverseFiniteHeadApproxInKerOrthogonal
      S g hη

/-- Helper for Theorem 2.19: finitely many singular-head bias factors can be made uniformly
small along `δ → 0⁺`. -/
theorem finiteHeadBiasEventuallySmall
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (F : Finset S.Index) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      ∀ j ∈ F, |w (αChoice δ) (S.singularValue j ^ 2) - 1| ≤ ε := by
  classical
  refine Finset.induction_on F ?_ ?_
  · -- The empty head has no coordinates to control.
    filter_upwards [self_mem_nhdsWithin] with δ hδ j hj
    simp at hj
  · intro j F hjF hF
    have hj :
        ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
          |w (αChoice δ) (S.singularValue j ^ 2) - 1| < ε := by
      have hcomp :
          Tendsto
            (fun δ : ℝ ↦ w (αChoice δ) (S.singularValue j ^ 2))
            (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
        -- Compose the parameter choice with the pointwise scalar convergence at the `j`-th mode.
        exact (h_pointwise (S.singularValue j) (S.singularValue_pos j)).comp h_choice
      have habs :
          Tendsto
            (fun δ : ℝ ↦ |w (αChoice δ) (S.singularValue j ^ 2) - 1|)
            (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
        -- Move to the absolute-value error, where an `ε`-ball is the desired bias bound.
        have hcont : Continuous fun x : ℝ ↦ |x - 1| := by
          continuity
        have habs0 : Tendsto (fun x : ℝ ↦ |x - 1|) (𝓝 1) (𝓝 (|1 - 1|)) :=
          hcont.continuousAt.tendsto
        simpa [Function.comp_def] using habs0.comp hcomp
      exact (tendsto_order.1 habs).2 ε hε
    filter_upwards [hj, hF] with δ hδj hδF k hk
    by_cases hkj : k = j
    · subst hkj
      exact hδj.le
    · exact hδF k (by simpa [Finset.mem_insert, hkj, hjF] using hk)

/-- Helper for Theorem 2.19: composing the finite-head bias eventuality with a concrete positive
sequence yields an eventual finite-head bias bound along that sequence. -/
theorem finiteHeadBiasAlongChoiceSequence
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (F : Finset S.Index) {ε : ℝ} (hε : 0 < ε)
    (δSeq : ℕ → ℝ)
    (hδSeq : Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0))) :
    ∀ᶠ n in atTop, ∀ j ∈ F, |w (αChoice (δSeq n)) (S.singularValue j ^ 2) - 1| ≤ ε := by
  -- Compose the neighborhood-level finite-head bias control with the concrete positive sequence.
  exact hδSeq.eventually
    (finiteHeadBiasEventuallySmall S w lα αChoice h_choice h_pointwise F hε)

/-- Helper for Theorem 2.19: once the stagewise head approximation, data-tail estimate, and
finite-head exact-data estimate all decay geometrically, the exact-data reconstructions converge to
`(K.kerOrthogonalEquivRange.symm g : H₁)`. -/
theorem exactDataConvergesAlongChoice
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (g : K.range) (δSeq : ℕ → ℝ) (xSeq : ℕ → K.kerᗮ)
    (happrox :
      ∀ n, ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xSeq n : H₁)‖ ≤ (1 / 4 : ℝ) ^ n)
    (hdata :
      ∀ n, ‖(g : H₂) - K (xSeq n : H₁)‖ ≤ δSeq n)
    (hnormSeq :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * δSeq n ≤
          (1 / 4 : ℝ) ^ n)
    (hhead :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δSeq n)) (K (xSeq n : H₁)) -
            (xSeq n : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n) :
    Tendsto
      (fun n ↦ S.reconstructionFamily w h_bound (αChoice (δSeq n)) (g : H₂))
      atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  have hpow :
      Tendsto (fun n : ℕ ↦ (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    -- The geometric error scale decays to `0`.
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hthreePow :
      Tendsto (fun n : ℕ ↦ (3 : ℝ) * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    -- The sum of the three geometric error terms still decays to `0`.
    simpa using (tendsto_const_nhds.mul hpow)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hthreePow ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  let Rn := S.reconstructionFamily w h_bound (αChoice (δSeq n))
  have hsplit :
      ‖Rn (g : H₂) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
        ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖ +
          ‖Rn (K (xSeq n : H₁)) - (xSeq n : H₁)‖ +
            ‖(xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
    -- Compare the exact-data reconstruction with the finite head `xSeq n`.
    have hdecomp :
        Rn (g : H₂) - (K.kerOrthogonalEquivRange.symm g : H₁) =
          (Rn (g : H₂) - Rn (K (xSeq n : H₁))) +
            ((Rn (K (xSeq n : H₁)) - (xSeq n : H₁)) +
              ((xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁))) := by
      simp [Rn, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hdecomp]
    calc
      ‖(Rn (g : H₂) - Rn (K (xSeq n : H₁))) +
          ((Rn (K (xSeq n : H₁)) - (xSeq n : H₁)) +
            ((xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)))‖
          ≤ ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖ +
              ‖(Rn (K (xSeq n : H₁)) - (xSeq n : H₁)) +
                ((xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁))‖ := by
            exact norm_add_le _ _
      _ ≤ ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖ +
            (‖Rn (K (xSeq n : H₁)) - (xSeq n : H₁)‖ +
              ‖(xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖ +
            ‖Rn (K (xSeq n : H₁)) - (xSeq n : H₁)‖ +
              ‖(xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
            ring
  have htail :
      ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖ ≤ (1 / 4 : ℝ) ^ n := by
    -- The data-tail term is controlled by the operator norm times the chosen tail radius.
    calc
      ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖
          ≤ ‖Rn‖ * ‖(g : H₂) - K (xSeq n : H₁)‖ := by
            simpa [Rn] using
              reconstructionFamily_apply_sub_le
                S w h_bound (αChoice (δSeq n)) (g : H₂) (K (xSeq n : H₁))
      _ ≤ ‖Rn‖ * δSeq n := by
            exact mul_le_mul_of_nonneg_left (hdata n) (norm_nonneg _)
      _ ≤ (1 / 4 : ℝ) ^ n := hnormSeq n
  have happrox' :
      ‖(xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤ (1 / 4 : ℝ) ^ n := by
    simpa [norm_sub_rev] using happrox n
  have hsumBound :
      ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖ +
          ‖Rn (K (xSeq n : H₁)) - (xSeq n : H₁)‖ +
            ‖(xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n := by
    -- Bound each of the three pieces by the geometric stage tolerance.
    exact add_le_add (add_le_add htail (hhead n)) happrox'
  calc
    dist (Rn (g : H₂)) (K.kerOrthogonalEquivRange.symm g : H₁)
        = ‖Rn (g : H₂) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
          rw [dist_eq_norm]
    _ ≤ ‖Rn (g : H₂) - Rn (K (xSeq n : H₁))‖ +
          ‖Rn (K (xSeq n : H₁)) - (xSeq n : H₁)‖ +
            ‖(xSeq n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := hsplit
    _ ≤ (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n := hsumBound
    _ = (3 : ℝ) * (1 / 4 : ℝ) ^ n := by ring
    _ < ε := by
          have hN' := hN n hn
          simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg, mul_nonneg] using hN'

/-- Helper for Theorem 2.19: the final exact-data convergence argument only needs the three
stagewise norm bounds that appear in the triangle inequality. -/
theorem exactDataConvergesFromNormalizedSchedule
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αStage : ℕ → ι) (g : K.range) (xStage : ℕ → K.kerᗮ)
    (happrox :
      ∀ n, ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xStage n : H₁)‖ ≤ (1 / 4 : ℝ) ^ n)
    (htail :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αStage n) (g : H₂) -
            S.reconstructionFamily w h_bound (αStage n) (K (xStage n : H₁))‖ ≤
          (1 / 4 : ℝ) ^ n)
    (hhead :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αStage n) (K (xStage n : H₁)) -
            (xStage n : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n) :
    Tendsto
      (fun n ↦ S.reconstructionFamily w h_bound (αStage n) (g : H₂))
      atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  have hpow :
      Tendsto (fun n : ℕ ↦ (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    -- The geometric stage tolerance decays to `0`.
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hthreePow :
      Tendsto (fun n : ℕ ↦ (3 : ℝ) * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    -- Summing the three geometric error terms preserves convergence to `0`.
    simpa using (tendsto_const_nhds.mul hpow)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hthreePow ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  let Rn := S.reconstructionFamily w h_bound (αStage n)
  have hsplit :
      ‖Rn (g : H₂) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
        ‖Rn (g : H₂) - Rn (K (xStage n : H₁))‖ +
          ‖Rn (K (xStage n : H₁)) - (xStage n : H₁)‖ +
            ‖(xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
    -- Compare the exact-data reconstruction with the finite head `xStage n`.
    have hdecomp :
        Rn (g : H₂) - (K.kerOrthogonalEquivRange.symm g : H₁) =
          (Rn (g : H₂) - Rn (K (xStage n : H₁))) +
            ((Rn (K (xStage n : H₁)) - (xStage n : H₁)) +
              ((xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁))) := by
      simp [Rn, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hdecomp]
    calc
      ‖(Rn (g : H₂) - Rn (K (xStage n : H₁))) +
          ((Rn (K (xStage n : H₁)) - (xStage n : H₁)) +
            ((xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)))‖
          ≤ ‖Rn (g : H₂) - Rn (K (xStage n : H₁))‖ +
              ‖(Rn (K (xStage n : H₁)) - (xStage n : H₁)) +
                ((xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁))‖ := by
            exact norm_add_le _ _
      _ ≤ ‖Rn (g : H₂) - Rn (K (xStage n : H₁))‖ +
            (‖Rn (K (xStage n : H₁)) - (xStage n : H₁)‖ +
              ‖(xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = ‖Rn (g : H₂) - Rn (K (xStage n : H₁))‖ +
            ‖Rn (K (xStage n : H₁)) - (xStage n : H₁)‖ +
              ‖(xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
            ring
  have happrox' :
      ‖(xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤ (1 / 4 : ℝ) ^ n := by
    simpa [norm_sub_rev] using happrox n
  have hsumBound :
      ‖Rn (g : H₂) - Rn (K (xStage n : H₁))‖ +
          ‖Rn (K (xStage n : H₁)) - (xStage n : H₁)‖ +
            ‖(xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n := by
    -- Bound the three triangle-inequality pieces by the geometric stage tolerance.
    exact add_le_add (add_le_add (htail n) (hhead n)) happrox'
  calc
    dist (Rn (g : H₂)) (K.kerOrthogonalEquivRange.symm g : H₁)
        = ‖Rn (g : H₂) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
          rw [dist_eq_norm]
    _ ≤ ‖Rn (g : H₂) - Rn (K (xStage n : H₁))‖ +
          ‖Rn (K (xStage n : H₁)) - (xStage n : H₁)‖ +
            ‖(xStage n : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := hsplit
    _ ≤ (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ n := hsumBound
    _ = (3 : ℝ) * (1 / 4 : ℝ) ^ n := by ring
    _ < ε := by
          have hN' := hN n hn
          simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg, mul_nonneg] using hN'

/-- Helper for Theorem 2.19: every right-neighborhood of `0` contains a whole interval
`(0, u)`. -/
theorem exists_Ioo_subset_of_mem_nhdsWithin_zero
    {U : Set ℝ} (hU : U ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) :
    ∃ u > 0, Set.Ioo 0 u ⊆ U := by
  -- Reinterpret the right-neighborhood of `0` through the standard `𝓝[>] 0` basis.
  rcases
      (mem_nhdsGT_iff_exists_Ioo_subset' zero_lt_one).1
        (by simpa using hU) with
    ⟨u, hu, hsubset⟩
  exact ⟨u, hu, hsubset⟩

/-- Helper for Theorem 2.19: a finite-head bias eventuality can be converted into a concrete
right-neighborhood interval `(0, u)`. -/
theorem finiteHeadBiasRadius
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (F : Finset S.Index) {ε : ℝ} (hε : 0 < ε) :
    ∃ u > 0, ∀ ⦃δ : ℝ⦄, δ ∈ Set.Ioo 0 u →
      ∀ j ∈ F, |w (αChoice δ) (S.singularValue j ^ 2) - 1| ≤ ε := by
  let U : Set ℝ :=
    {δ | ∀ j ∈ F, |w (αChoice δ) (S.singularValue j ^ 2) - 1| ≤ ε}
  have hU : U ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    -- Recast the eventual finite-head bias estimate as membership in a neighborhood set.
    change
      ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ j ∈ F, |w (αChoice δ) (S.singularValue j ^ 2) - 1| ≤ ε
    exact
      finiteHeadBiasEventuallySmall S w lα αChoice h_choice h_pointwise F hε
  rcases exists_Ioo_subset_of_mem_nhdsWithin_zero hU with ⟨u, hu, hsubset⟩
  refine ⟨u, hu, ?_⟩
  intro δ hδ j hj
  exact hsubset hδ j hj

/-- Helper for Theorem 2.19: under `S.length = ⊤`, the canonical `N`-mode head of the range
pseudoinverse is the finite right-basis sum over the first `N` `natIndex` modes. -/
def initialSegmentRangePseudoInverse
    (S : SingularSystem K) (g : K.range)
    (h_length : S.length = ⊤) (N : ℕ) : K.kerᗮ :=
  Finset.sum ((Finset.range N).image (S.natIndex h_length)) fun j ↦
    ((inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j) •
      (S.rightBasis j : K.kerᗮ))

/-- Helper for Theorem 2.19: the canonical `N`-mode range-pseudoinverse head has no right-basis
coordinates outside the first `N` `natIndex` modes. -/
theorem initialSegmentRangePseudoInverse_support
    (S : SingularSystem K) (g : K.range)
  (h_length : S.length = ⊤) (N : ℕ) :
    ∀ j ∉ (Finset.range N).image (S.natIndex h_length),
      S.rightBasis.repr (S.initialSegmentRangePseudoInverse g h_length N) j = 0 := by
  intro j hj
  -- Read the Hilbert-basis coefficient of the finite head and use orthogonality off its support.
  dsimp [initialSegmentRangePseudoInverse]
  rw [HilbertBasis.repr_apply_apply, inner_sum]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hkj : j ≠ k := by
    intro hkj
    apply hj
    simpa [hkj] using hk
  rw [inner_smul_right]
  simp [S.rightBasis.orthonormal.inner_eq_zero hkj]

/-- Helper for Theorem 2.19: the canonical `natIndex` initial segments approximate both the range
pseudoinverse and the original exact datum. -/
theorem initialSegmentRangePseudoInverseApprox
    (S : SingularSystem K) (g : K.range)
    (h_length : S.length = ⊤) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ,
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ η ∧
      ‖(g : H₂) - K (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ η := by
  let F : ℕ → Finset S.Index := fun N ↦ (Finset.range N).image (S.natIndex h_length)
  let f : S.Index → H₁ := fun j ↦
    ((inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j) •
      (S.rightBasis j : H₁))
  let pinv : H₁ := (K.kerOrthogonalEquivRange.symm g : H₁)
  have hFmono : Monotone F := by
    intro m n hmn j hj
    rcases Finset.mem_image.1 hj with ⟨i, hi, rfl⟩
    refine Finset.mem_image.2 ?_
    exact ⟨i, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hmn), rfl⟩
  have hFcover : ∀ j : S.Index, ∃ N, j ∈ F N := by
    intro j
    have hj_lt : (j : ℕ∞) < ⊤ := by
      simpa [h_length] using j.2
    have hj_eq : S.natIndex h_length ((j : ℕ∞).toNat) = j := by
      apply Subtype.ext
      simp [ENat.coe_toNat (ne_of_lt hj_lt)]
    refine ⟨(j : ℕ∞).toNat + 1, Finset.mem_image.2 ?_⟩
    exact ⟨(j : ℕ∞).toNat, Finset.mem_range.2 (Nat.lt_succ_self _), hj_eq⟩
  have hFtendsto : Tendsto F atTop atTop := by
    exact hFmono.tendsto_atTop_finset hFcover
  have hsum : HasSum f pinv := by
    -- Expand the range pseudoinverse into the right-basis coefficient series.
    simpa [f, pinv] using hasSum_partialPseudoInverseOnRange S g
  have hsumH₁ :
      Tendsto (fun N ↦ Finset.sum (F N) fun j ↦ f j) atTop (𝓝 pinv) := by
    -- Compose the full `HasSum` with the cofinal `natIndex` initial-segment family.
    exact hsum.comp hFtendsto
  have hmap : K pinv = (g : H₂) := by
    -- Applying `K` to the range pseudoinverse recovers the exact datum.
    simpa [pinv] using map_partialPseudoInverseOnRange g
  have hsumMap :
      HasSum (fun j : S.Index ↦ K (f j)) (g : H₂) := by
    -- Map the same coefficient series through `K` to recover the datum series.
    simpa [f, hmap] using hsum.mapL K
  have hsumH₂ :
      Tendsto (fun N ↦ Finset.sum (F N) fun j ↦ K (f j)) atTop (𝓝 (g : H₂)) := by
    -- The mapped initial segments therefore converge to `g`.
    exact hsumMap.comp hFtendsto
  have hH₁ :
      ∀ᶠ N : ℕ in atTop,
        ‖pinv - Finset.sum (F N) (fun j ↦ f j)‖ < η := by
    -- Eventually the canonical initial segments are `η`-close to the range pseudoinverse.
    filter_upwards [hsumH₁.eventually (Metric.ball_mem_nhds pinv hη)] with N hN
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hN
  have hH₂ :
      ∀ᶠ N : ℕ in atTop,
        ‖(g : H₂) - Finset.sum (F N) (fun j ↦ K (f j))‖ < η := by
    -- The same initial segments map to `η`-close approximations of the datum.
    filter_upwards [hsumH₂.eventually (Metric.ball_mem_nhds (g : H₂) hη)] with N hN
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hN
  rcases Filter.mem_atTop_sets.1 (hH₁.and hH₂) with ⟨N, hN⟩
  specialize hN N le_rfl
  rcases hN with ⟨hN₁, hN₂⟩
  refine ⟨N, ?_, ?_⟩
  · -- Reinterpret the `H₁` partial sum as the subtype-valued canonical initial segment.
    have hhead :
        ((S.initialSegmentRangePseudoInverse g h_length N : K.kerᗮ) : H₁) =
          Finset.sum (F N) (fun j ↦ f j) := by
      simp [initialSegmentRangePseudoInverse, F, f]
    have hN₁' := hN₁.le
    simpa [hhead] using hN₁'
  · -- Rewrite the mapped partial sum through the same canonical initial segment.
    have hheadMap :
        K (S.initialSegmentRangePseudoInverse g h_length N : H₁) =
          Finset.sum (F N) (fun j ↦ K (f j)) := by
      simp [initialSegmentRangePseudoInverse, F, f, map_sum]
    have hN₂' := hN₂.le
    simpa [hheadMap] using hN₂'

/-- Helper for Theorem 2.19: once the canonical `natIndex` initial segments are far enough out,
every later head approximates both the range pseudoinverse and the original exact datum with the
same prescribed tolerance. -/
theorem initialSegmentRangePseudoInverseApproxEventually
    (S : SingularSystem K) (g : K.range)
    (h_length : S.length = ⊤) {η : ℝ} (hη : 0 < η) :
    ∃ N0 : ℕ,
      ∀ N ≥ N0,
        ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
            (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ η ∧
          ‖(g : H₂) - K (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ η := by
  let F : ℕ → Finset S.Index := fun N ↦ (Finset.range N).image (S.natIndex h_length)
  let f : S.Index → H₁ := fun j ↦
    ((inner ℝ (S.leftBasis j : H₂) (g : H₂) / S.singularValue j) •
      (S.rightBasis j : H₁))
  let pinv : H₁ := (K.kerOrthogonalEquivRange.symm g : H₁)
  have hFmono : Monotone F := by
    intro m n hmn j hj
    rcases Finset.mem_image.1 hj with ⟨i, hi, rfl⟩
    refine Finset.mem_image.2 ?_
    exact ⟨i, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hmn), rfl⟩
  have hFcover : ∀ j : S.Index, ∃ N, j ∈ F N := by
    intro j
    have hj_lt : (j : ℕ∞) < ⊤ := by
      simpa [h_length] using j.2
    have hj_eq : S.natIndex h_length ((j : ℕ∞).toNat) = j := by
      apply Subtype.ext
      simp [ENat.coe_toNat (ne_of_lt hj_lt)]
    refine ⟨(j : ℕ∞).toNat + 1, Finset.mem_image.2 ?_⟩
    exact ⟨(j : ℕ∞).toNat, Finset.mem_range.2 (Nat.lt_succ_self _), hj_eq⟩
  have hFtendsto : Tendsto F atTop atTop := by
    -- The canonical initial-segment supports are cofinal among finite singular heads.
    exact hFmono.tendsto_atTop_finset hFcover
  have hsum : HasSum f pinv := by
    -- Expand the range pseudoinverse in the right-basis coefficient series.
    simpa [f, pinv] using hasSum_partialPseudoInverseOnRange S g
  have hsumH₁ :
      Tendsto (fun N ↦ Finset.sum (F N) fun j ↦ f j) atTop (𝓝 pinv) := by
    -- Compose the full series convergence with the cofinal canonical-head family.
    exact hsum.comp hFtendsto
  have hmap : K pinv = (g : H₂) := by
    -- Applying `K` to the range pseudoinverse recovers the exact datum.
    simpa [pinv] using map_partialPseudoInverseOnRange g
  have hsumMap :
      HasSum (fun j : S.Index ↦ K (f j)) (g : H₂) := by
    -- Mapping the same series through `K` gives the exact-datum expansion.
    simpa [f, hmap] using hsum.mapL K
  have hsumH₂ :
      Tendsto (fun N ↦ Finset.sum (F N) fun j ↦ K (f j)) atTop (𝓝 (g : H₂)) := by
    -- The mapped canonical heads therefore converge to `g`.
    exact hsumMap.comp hFtendsto
  have hH₁ :
      ∀ᶠ N : ℕ in atTop,
        ‖pinv - Finset.sum (F N) (fun j ↦ f j)‖ < η := by
    -- Eventually every canonical head is `η`-close to the range pseudoinverse.
    filter_upwards [hsumH₁.eventually (Metric.ball_mem_nhds pinv hη)] with N hN
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hN
  have hH₂ :
      ∀ᶠ N : ℕ in atTop,
        ‖(g : H₂) - Finset.sum (F N) (fun j ↦ K (f j))‖ < η := by
    -- The same heads map to `η`-close approximations of the exact datum.
    filter_upwards [hsumH₂.eventually (Metric.ball_mem_nhds (g : H₂) hη)] with N hN
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hN
  rcases Filter.mem_atTop_sets.1 (hH₁.and hH₂) with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hNN0
  have hN := hN0 N hNN0
  rcases hN with ⟨hN₁, hN₂⟩
  constructor
  · -- Rewrite the ambient `H₁` partial sum as the canonical subtype-valued head.
    have hhead :
        ((S.initialSegmentRangePseudoInverse g h_length N : K.kerᗮ) : H₁) =
          Finset.sum (F N) (fun j ↦ f j) := by
      simp [initialSegmentRangePseudoInverse, F, f]
    simpa [hhead] using hN₁.le
  · -- Rewrite the mapped partial sum through the same canonical head.
    have hheadMap :
        K (S.initialSegmentRangePseudoInverse g h_length N : H₁) =
          Finset.sum (F N) (fun j ↦ K (f j)) := by
      simp [initialSegmentRangePseudoInverse, F, f, map_sum]
    simpa [hheadMap] using hN₂.le

/-- Helper for Theorem 2.19: every canonical initial segment is norm-controlled by the full
range pseudoinverse. -/
theorem initialSegmentRangePseudoInverse_norm_le
    (S : SingularSystem K) (g : K.range)
    (h_length : S.length = ⊤) (N : ℕ) :
    ‖(S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤
      ‖(K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
  let F : Finset S.Index := (Finset.range N).image (S.natIndex h_length)
  let c : lp (fun _ : S.Index ↦ ℝ) 2 :=
    S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g)
  let m : S.Index → ℝ := fun j ↦ if j ∈ F then 1 else 0
  have hmul :
      ∀ j : S.Index, ‖ContinuousLinearMap.mul ℝ ℝ (m j)‖ ≤ 1 := by
    intro j
    -- The truncation multiplier is either `0` or `1`, so its operator norm is at most `1`.
    rw [ContinuousLinearMap.opNorm_mul_apply]
    by_cases hj : j ∈ F
    · simp [m, hj, Real.norm_eq_abs]
    · simp [m, hj, Real.norm_eq_abs]
  let D : lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    lp.mapCLM 2 (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (m j)) zero_le_one hmul
  let y : K.kerᗮ := S.rightBasis.repr.symm (D c)
  let eSub : S.Index → K.kerᗮ := fun j ↦
    (if j ∈ F then S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j else 0) •
      (S.rightBasis j : K.kerᗮ)
  have hdiagSubtype :
      HasSum
        (fun j : S.Index ↦ (D c j) • (S.rightBasis j : K.kerᗮ))
        y := by
    -- Expand the truncated coordinate vector back in the right Hilbert basis.
    simpa [c, y] using S.rightBasis.hasSum_repr_symm (D c)
  have hdiagSub :
      HasSum eSub y := by
    -- Rewrite the diagonal map as the finite-support truncation while staying in `K.kerᗮ`.
    refine HasSum.congr_fun hdiagSubtype ?_
    intro j
    have hDc :
        D c j =
          if j ∈ F then S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j else 0 := by
      -- Unfold the diagonal truncation on the `j`-th coordinate.
      simp [D, c, m]
    -- Rewrite the coefficient and then fold back to the `eSub` notation.
    simpa [eSub] using congrArg (fun a : ℝ ↦ a • (S.rightBasis j : K.kerᗮ)) hDc.symm
  have hfiniteSub : HasSum eSub (Finset.sum F eSub) := by
    -- A function supported on `F` sums to the finite right-basis head over `F`.
    refine hasSum_sum_of_ne_finset_zero ?_
    intro j hj
    simp [eSub, hj]
  have hheadSub :
      S.initialSegmentRangePseudoInverse g h_length N =
        Finset.sum F eSub := by
    -- Rewrite the canonical initial segment in `K.kerᗮ` through the pseudoinverse coordinates.
    rw [initialSegmentRangePseudoInverse]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [(partialPseudoInverseOnRange_repr S g j).symm]
    simp [eSub, hj]
  have hySub :
      y = S.initialSegmentRangePseudoInverse g h_length N := by
    -- The diagonal truncation and the canonical initial segment have the same right-basis series.
    rw [hheadSub]
    exact hdiagSub.unique hfiniteSub
  have hy :
      ((y : K.kerᗮ) : H₁) = (S.initialSegmentRangePseudoInverse g h_length N : H₁) := by
    -- Forget the subtype after identifying the truncated vector with the canonical head.
    simpa using congrArg (fun z : K.kerᗮ ↦ (z : H₁)) hySub
  have hDnorm : ‖D‖ ≤ 1 := by
    -- The coordinatewise truncation operator is a contraction on `ℓ²`.
    exact lp.norm_mapCLM_le 2
      (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (m j))
      zero_le_one
      hmul
  have hc :
      ‖c‖ = ‖(K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
    -- `c` is exactly the right-basis coefficient vector of the range pseudoinverse.
    simp [c]
  calc
    ‖(S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ = ‖((y : K.kerᗮ) : H₁)‖ := by
      rw [hy]
    _ = ‖y‖ := by
      rfl
    _ = ‖D c‖ := by
      simp [y]
    _ ≤ ‖D‖ * ‖c‖ := by
      exact D.le_opNorm c
    _ ≤ 1 * ‖c‖ := by
      exact mul_le_mul_of_nonneg_right hDnorm (norm_nonneg c)
    _ = ‖(K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
      simpa [hc]

/-- Helper for Theorem 2.19: the canonical `N`-mode range-pseudoinverse head is the finite
right-basis truncation of the full range pseudoinverse. -/
theorem initialSegmentRangePseudoInverse_eq_reprSum
    (S : SingularSystem K) (g : K.range)
    (h_length : S.length = ⊤) (N : ℕ) :
    S.initialSegmentRangePseudoInverse g h_length N =
      Finset.sum ((Finset.range N).image (S.natIndex h_length)) fun j ↦
        (S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j) •
          (S.rightBasis j : K.kerᗮ) := by
  -- Rewrite the explicit coefficient formula through the right-basis coordinates of the
  -- range pseudoinverse.
  rw [initialSegmentRangePseudoInverse]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [(partialPseudoInverseOnRange_repr S g j).symm]

/-- Helper for Theorem 2.19: truncating any `K.kerᗮ` vector to finitely many right-basis
coordinates does not increase its norm. -/
theorem rightBasisFiniteProjection_norm_le
    (S : SingularSystem K) (F : Finset S.Index) (x : K.kerᗮ) :
    ‖(Finset.sum F fun j ↦
        (S.rightBasis.repr x j) • (S.rightBasis j : K.kerᗮ) : K.kerᗮ)‖ ≤ ‖x‖ := by
  let c : lp (fun _ : S.Index ↦ ℝ) 2 := S.rightBasis.repr x
  let m : S.Index → ℝ := fun j ↦ if j ∈ F then 1 else 0
  have hmul :
      ∀ j : S.Index, ‖ContinuousLinearMap.mul ℝ ℝ (m j)‖ ≤ 1 := by
    intro j
    -- The coordinate multiplier is either `0` or `1`, so its operator norm is at most `1`.
    rw [ContinuousLinearMap.opNorm_mul_apply]
    by_cases hj : j ∈ F
    · simp [m, hj]
    · simp [m, hj]
  let D : lp (fun _ : S.Index ↦ ℝ) 2 →L[ℝ] lp (fun _ : S.Index ↦ ℝ) 2 :=
    lp.mapCLM 2 (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (m j)) zero_le_one hmul
  let y : K.kerᗮ := S.rightBasis.repr.symm (D c)
  let eSub : S.Index → K.kerᗮ := fun j ↦
    (if j ∈ F then S.rightBasis.repr x j else 0) •
      (S.rightBasis j : K.kerᗮ)
  have hsum :
      (Finset.sum F fun j ↦
          (S.rightBasis.repr x j) • (S.rightBasis j : K.kerᗮ) : K.kerᗮ) =
        Finset.sum F eSub := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [eSub, hj]
  have hdiagSubtype :
      HasSum
        (fun j : S.Index ↦ (D c j) • (S.rightBasis j : K.kerᗮ))
        y := by
    -- Expand the truncated coordinate vector back in the right Hilbert basis.
    simpa [c, y] using S.rightBasis.hasSum_repr_symm (D c)
  have hdiagSub :
      HasSum eSub y := by
    -- Rewrite the diagonal truncation as the explicit finite-coordinate projection.
    refine HasSum.congr_fun hdiagSubtype ?_
    intro j
    have hDc :
        D c j =
          if j ∈ F then S.rightBasis.repr x j else 0 := by
      -- Unfold the diagonal truncation on the `j`-th coordinate.
      simp [D, c, m]
    simpa [eSub] using congrArg (fun a : ℝ ↦ a • (S.rightBasis j : K.kerᗮ)) hDc.symm
  have hfiniteSub : HasSum eSub (Finset.sum F eSub) := by
    -- A function supported on `F` sums to the finite right-basis projection over `F`.
    refine hasSum_sum_of_ne_finset_zero ?_
    intro j hj
    simp [eSub, hj]
  have hySub :
      y = Finset.sum F eSub := by
    -- The diagonal truncation and the explicit finite-coordinate projection have the same series.
    exact hdiagSub.unique hfiniteSub
  have hDnorm : ‖D‖ ≤ 1 := by
    -- The coordinatewise truncation is a contraction on `ℓ²`.
    exact lp.norm_mapCLM_le 2
      (fun j ↦ ContinuousLinearMap.mul ℝ ℝ (m j))
      zero_le_one
      hmul
  have hc : ‖c‖ = ‖x‖ := by
    -- `c` is exactly the right-basis coefficient vector of `x`.
    simp [c]
  calc
    ‖(Finset.sum F fun j ↦
          (S.rightBasis.repr x j) • (S.rightBasis j : K.kerᗮ) : K.kerᗮ)‖
        = ‖(Finset.sum F eSub : K.kerᗮ)‖ := by
          rw [hsum]
    _ = ‖y‖ := by
          rw [← hySub]
    _ = ‖D c‖ := by
          simp [y]
    _ ≤ ‖D‖ * ‖c‖ := by
          exact D.le_opNorm c
    _ ≤ 1 * ‖c‖ := by
          exact mul_le_mul_of_nonneg_right hDnorm (norm_nonneg c)
    _ = ‖x‖ := by
          simpa [hc]

/-- Helper for Theorem 2.19: on its supported singular modes, the canonical `N`-mode head has
the same right-basis coordinates as the full range pseudoinverse. -/
theorem initialSegmentRangePseudoInverse_repr_eq
    (S : SingularSystem K) (g : K.range)
    (h_length : S.length = ⊤) {N : ℕ} {j : S.Index}
    (hj :
      j ∈ (Finset.range N).image (S.natIndex h_length)) :
    S.rightBasis.repr (S.initialSegmentRangePseudoInverse g h_length N) j =
      S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j := by
  have hnorm : ‖(S.rightBasis j : K.kerᗮ)‖ = 1 := by
    -- Every right-basis vector has norm `1`.
    simpa using S.rightBasis.orthonormal.norm_eq_one j
  -- Rewrite the canonical head as the finite right-basis truncation of the full pseudoinverse.
  rw [S.initialSegmentRangePseudoInverse_eq_reprSum g h_length N]
  rw [HilbertBasis.repr_apply_apply, inner_sum]
  rw [Finset.sum_eq_single_of_mem j hj]
  · -- On the supported coordinate `j`, only the diagonal basis term survives.
    rw [inner_smul_right]
    simp [hnorm]
  · intro k hk hkj
    -- Off the diagonal, orthonormality kills every other summand in the finite head.
    rw [inner_smul_right]
    simp [S.rightBasis.orthonormal.inner_eq_zero hkj.symm]

/-- Helper for Theorem 2.19: later canonical heads move by at most the current tail of the full
range pseudoinverse. -/
theorem initialSegmentRangePseudoInverseDist_le_of_le
    (S : SingularSystem K) (g : K.range)
    (h_length : S.length = ⊤) {NCore NStage : ℕ}
    (hN : NCore ≤ NStage) :
    ‖(S.initialSegmentRangePseudoInverse g h_length NStage : H₁) -
        (S.initialSegmentRangePseudoInverse g h_length NCore : H₁)‖ ≤
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
          (S.initialSegmentRangePseudoInverse g h_length NCore : H₁)‖ := by
  let FCore : Finset S.Index := (Finset.range NCore).image (S.natIndex h_length)
  let FStage : Finset S.Index := (Finset.range NStage).image (S.natIndex h_length)
  let xCore : K.kerᗮ := S.initialSegmentRangePseudoInverse g h_length NCore
  let xStage : K.kerᗮ := S.initialSegmentRangePseudoInverse g h_length NStage
  have hproj :
      xStage - xCore =
        Finset.sum FStage fun j ↦
          (S.rightBasis.repr ((K.kerOrthogonalEquivRange.symm g) - xCore) j) •
            (S.rightBasis j : K.kerᗮ) := by
    -- Compare the stage difference with the projected tail on each right-basis coordinate.
    apply S.rightBasis.repr.injective
    ext j
    have hnormj : ‖(S.rightBasis j : K.kerᗮ)‖ = 1 := by
      -- Every right-basis vector again has unit norm on the coordinate being tested.
      simpa using S.rightBasis.orthonormal.norm_eq_one j
    have hreprStage :
        S.rightBasis.repr (xStage - xCore) j =
          S.rightBasis.repr xStage j - S.rightBasis.repr xCore j := by
      -- Read the stage difference through the linearity of the right-basis coordinates.
      simpa using
        congrArg (fun u : lp (fun _ : S.Index ↦ ℝ) 2 => u j)
          (map_sub (S.rightBasis.repr) xStage xCore)
    have hreprTail :
        S.rightBasis.repr ((K.kerOrthogonalEquivRange.symm g) - xCore) j =
          S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j -
            S.rightBasis.repr xCore j := by
      -- The same coordinate linearity identifies the tail coefficients.
      simpa using
        congrArg (fun u : lp (fun _ : S.Index ↦ ℝ) 2 => u j)
          (map_sub (S.rightBasis.repr) (K.kerOrthogonalEquivRange.symm g) xCore)
    by_cases hjStage : j ∈ FStage
    · have hsum :
          S.rightBasis.repr
              (Finset.sum FStage fun k ↦
                (S.rightBasis.repr ((K.kerOrthogonalEquivRange.symm g) - xCore) k) •
                  (S.rightBasis k : K.kerᗮ)) j =
            S.rightBasis.repr ((K.kerOrthogonalEquivRange.symm g) - xCore) j := by
        rw [HilbertBasis.repr_apply_apply, inner_sum, Finset.sum_eq_single_of_mem j hjStage]
        · -- On the stage support, the projection keeps exactly the `j`-th tail coordinate.
          rw [inner_smul_right]
          simp [hnormj]
        · intro k hk hkj
          -- Off the diagonal, orthonormality kills the other basis coordinates.
          rw [inner_smul_right]
          simp [S.rightBasis.orthonormal.inner_eq_zero hkj.symm]
      have hstage :
          S.rightBasis.repr xStage j =
            S.rightBasis.repr (K.kerOrthogonalEquivRange.symm g) j := by
        simpa [xStage, FStage] using
          S.initialSegmentRangePseudoInverse_repr_eq g h_length (N := NStage) hjStage
      -- On the larger support, the stage head matches the pseudoinverse coordinate exactly.
      rw [hreprStage, hsum, hreprTail, hstage]
    · have hsum :
          S.rightBasis.repr
              (Finset.sum FStage fun k ↦
                (S.rightBasis.repr ((K.kerOrthogonalEquivRange.symm g) - xCore) k) •
                  (S.rightBasis k : K.kerᗮ)) j =
            0 := by
        rw [HilbertBasis.repr_apply_apply, inner_sum]
        refine Finset.sum_eq_zero ?_
        intro k hk
        have hkj : j ≠ k := by
          intro hkj
          apply hjStage
          simpa [hkj] using hk
        -- Outside the chosen stage support, every basis summand is orthogonal to `j`.
        rw [inner_smul_right]
        simp [S.rightBasis.orthonormal.inner_eq_zero hkj]
      have hjCore : j ∉ FCore := by
        intro hjCore
        apply hjStage
        rcases Finset.mem_image.1 hjCore with ⟨i, hi, rfl⟩
        refine Finset.mem_image.2 ?_
        exact ⟨i, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hN), rfl⟩
      have hstage :
          S.rightBasis.repr xStage j = 0 := by
        simpa [xStage, FStage] using
          S.initialSegmentRangePseudoInverse_support g h_length NStage j hjStage
      have hcore :
          S.rightBasis.repr xCore j = 0 := by
        simpa [xCore, FCore] using
          S.initialSegmentRangePseudoInverse_support g h_length NCore j hjCore
      -- Outside the larger support, both canonical heads and the projected tail vanish.
      rw [hreprStage, hstage, hcore]
      simpa [hreprTail] using hsum.symm
  have hnorm :
      ‖xStage - xCore‖ ≤ ‖(K.kerOrthogonalEquivRange.symm g) - xCore‖ := by
    -- The stage difference is a finite right-basis projection of the remaining tail.
    rw [hproj]
    exact
      S.rightBasisFiniteProjection_norm_le
        FStage
        ((K.kerOrthogonalEquivRange.symm g) - xCore)
  -- Forget the subtype notation and rewrite both norms in the ambient Hilbert space.
  simpa [xStage, xCore, norm_sub_rev] using hnorm

/-- Helper for Theorem 2.19: under `S.length = ⊤`, one can ask for the bias bound on the first
`N` canonical singular modes at once. -/
theorem initialSegmentBiasRadius
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_length : S.length = ⊤) (N : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ u > 0, ∀ ⦃δ : ℝ⦄, δ ∈ Set.Ioo 0 u →
      ∀ i < N, |w (αChoice δ) (S.singularValue (S.natIndex h_length i) ^ 2) - 1| ≤ B := by
  let F : Finset S.Index := (Finset.range N).image (S.natIndex h_length)
  obtain ⟨u, hu, huBias⟩ :=
    finiteHeadBiasRadius S w lα αChoice h_choice h_pointwise F hB
  refine ⟨u, hu, ?_⟩
  intro δ hδ i hi
  have hiF : S.natIndex h_length i ∈ F := by
    refine Finset.mem_image.2 ?_
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩
  -- Repackage the finite-head bias radius on the image set as an initial-segment statement.
  exact huBias hδ _ hiF

/-- Helper for Theorem 2.19: the norm-based finite-head stage estimate specializes cleanly to
canonical initial segments. -/
theorem exactDataStageFromInitialSegmentBudgetNorm
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) (h_length : S.length = ⊤) (N : ℕ)
    {δ ηApprox ηTail ηHead B : ℝ} (hB0 : 0 ≤ B)
    (happrox :
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ ηApprox)
    (hdata :
      ‖(g : H₂) - K (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ δ)
    (hB :
      ∀ i < N,
        |w α (S.singularValue (S.natIndex h_length i) ^ 2) - 1| ≤ B)
    (hheadBudget :
      B * ‖(S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ ηHead)
    (hnorm :
      ‖S.reconstructionFamily w h_bound α‖ * δ ≤ ηTail) :
    ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
        (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ ηApprox ∧
      ‖S.reconstructionFamily w h_bound α (g : H₂) -
          S.reconstructionFamily w h_bound α
            (K (S.initialSegmentRangePseudoInverse g h_length N : H₁))‖ ≤ ηTail ∧
      ‖S.reconstructionFamily w h_bound α
            (K (S.initialSegmentRangePseudoInverse g h_length N : H₁)) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ ηHead := by
  let F : Finset S.Index := (Finset.range N).image (S.natIndex h_length)
  let xN : K.kerᗮ := S.initialSegmentRangePseudoInverse g h_length N
  have hsupport :
      ∀ j ∉ F, S.rightBasis.repr xN j = 0 := by
    -- The canonical initial segment is supported exactly on the first `N` `natIndex` modes.
    simpa [F, xN] using S.initialSegmentRangePseudoInverse_support g h_length N
  have hBsupport :
      ∀ j ∈ F, |w α (S.singularValue j ^ 2) - 1| ≤ B := by
    intro j hj
    rcases Finset.mem_image.1 hj with ⟨i, hi, rfl⟩
    -- Repackage the initial-segment bias hypothesis on image coordinates as a supportwise bound.
    exact hB i (Finset.mem_range.1 hi)
  -- Invoke the generic finite-head stage theorem on the canonical initial segment.
  simpa [F, xN] using
    exactDataStageFromFiniteHeadBudgetNorm
      S w h_bound g α F xN hsupport B hB0 happrox hdata hBsupport hheadBudget hnorm

/-- Helper for Theorem 2.19: the norm-product hypothesis can be converted into a concrete
right-neighborhood interval `(0, u)`. -/
theorem normProductRadius
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u > 0, ∀ ⦃δ : ℝ⦄, δ ∈ Set.Ioo 0 u →
      ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ ≤ ε := by
  let U : Set ℝ :=
    {δ | ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ < ε}
  have hU : U ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    -- Recast the convergence-to-zero hypothesis as membership in an upper-radius neighborhood.
    change
      ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ < ε
    exact (tendsto_order.1 h_norm).2 ε hε
  rcases exists_Ioo_subset_of_mem_nhdsWithin_zero hU with ⟨u, hu, hsubset⟩
  refine ⟨u, hu, ?_⟩
  intro δ hδ
  exact (hsubset hδ).le

/-- Helper for Theorem 2.19: the geometric choice `δ_n = (1 / 2)^n` tends to `0` through
positive radii. -/
theorem geometricChoiceTendstoWithinZero :
    Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  have hpow :
      Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) := by
    -- The geometric radii converge to `0` in the ordinary topology.
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  -- Upgrade the ordinary limit to a right-sided limit using positivity of every term.
  refine
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) hpow ?_
  exact Filter.Eventually.of_forall fun n ↦ by
    change 0 < (1 / 2 : ℝ) ^ n
    exact pow_pos (by norm_num) n

/-- Helper for Theorem 2.19: the norm-product hypothesis yields a concrete positive parameter
sequence whose norm products already satisfy the geometric target bounds. -/
theorem existsNormControlledChoiceSequence
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    ∃ δSeq : ℕ → ℝ,
      (∀ n, 0 < δSeq n) ∧
      Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0)) ∧
      (∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * δSeq n ≤
          (1 / 4 : ℝ) ^ n) := by
  choose u huPos huBound using
    fun n ↦
      normProductRadius
        S w h_bound αChoice h_norm (hε := by
          exact pow_pos (by norm_num : (0 : ℝ) < 1 / 4) n)
  let δSeq : ℕ → ℝ := fun n ↦ min ((1 / 2 : ℝ) ^ n) (u n / 2)
  have hδPos : ∀ n, 0 < δSeq n := by
    intro n
    -- Both comparison radii are positive, so their minimum is positive.
    dsimp [δSeq]
    refine lt_min ?_ ?_
    · positivity
    · have hu : 0 < u n := huPos n
      linarith
  have hδNorm : ∀ n,
      ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * δSeq n ≤
        (1 / 4 : ℝ) ^ n := by
    intro n
    have hmem : δSeq n ∈ Set.Ioo 0 (u n) := by
      -- The chosen parameter lies inside the norm-product radius returned for stage `n`.
      constructor
      · exact hδPos n
      · calc
          δSeq n ≤ u n / 2 := by
            dsimp [δSeq]
            exact min_le_right _ _
          _ < u n := by
            linarith [huPos n]
    exact huBound n hmem
  have hδToZero : Tendsto δSeq atTop (𝓝 (0 : ℝ)) := by
    -- The norm-controlled parameters are squeezed by the geometric reference radii.
    refine squeeze_zero (g := fun n : ℕ ↦ (1 / 2 : ℝ) ^ n)
      (fun n ↦ le_of_lt (hδPos n)) ?_ ?_
    · intro n
      dsimp [δSeq]
      exact min_le_left _ _
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hδWithin : ∀ᶠ n : ℕ in atTop, δSeq n ∈ Set.Ioi 0 := by
    -- Positivity of every chosen parameter upgrades the ordinary limit to a right-sided one.
    exact Filter.Eventually.of_forall fun n ↦ hδPos n
  refine ⟨δSeq, hδPos, ?_, hδNorm⟩
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within δSeq hδToZero hδWithin

/-- Helper for Theorem 2.19: one exact-data stage should simultaneously approximate the
range pseudoinverse, control the pure tail perturbation, control the finite-head exact-data
reconstruction error, and satisfy the norm-product bound. -/
theorem exactDataStageFiniteLength
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) {ε : ℝ} (hε : 0 < ε)
    (h_length : S.length ≠ ⊤) :
    ∃ δ > 0, ∃ x : K.kerᗮ,
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (x : H₁)‖ ≤ ε ∧
      ‖S.reconstructionFamily w h_bound (αChoice δ) (g : H₂) -
          S.reconstructionFamily w h_bound (αChoice δ) (K (x : H₁))‖ ≤ ε ∧
      ‖S.reconstructionFamily w h_bound (αChoice δ) (K (x : H₁)) - (x : H₁)‖ ≤ ε ∧
      ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ ≤ ε := by
  classical
  haveI : Finite S.Index := S.finiteIndexOfLengthNeTop h_length
  -- Convert the finite singular-length hypothesis into an explicit finite index type.
  letI : Fintype S.Index := Fintype.ofFinite S.Index
  let x : K.kerᗮ := K.kerOrthogonalEquivRange.symm g
  let pinv : H₁ := (K.kerOrthogonalEquivRange.symm g : H₁)
  let B : ℝ := ε / max ‖pinv‖ 1
  have hBpos : 0 < B := by
    -- The finite-head bias radius can use a fixed positive tolerance because `max ‖pinv‖ 1 > 0`.
    have hmax : 0 < max ‖pinv‖ 1 := by
      exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact div_pos hε hmax
  have hB0 : 0 ≤ B := hBpos.le
  obtain ⟨uBias, huBiasPos, huBias⟩ :=
    finiteHeadBiasRadius S w lα αChoice h_choice h_pointwise Finset.univ hBpos
  obtain ⟨uNorm, huNormPos, huNorm⟩ :=
    normProductRadius S w h_bound αChoice h_norm hε
  let δ : ℝ := min (uBias / 2) (uNorm / 2)
  have hδPos : 0 < δ := by
    -- Halving both admissible radii keeps the chosen parameter positive.
    dsimp [δ]
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hδBias : δ ∈ Set.Ioo 0 uBias := by
    -- The chosen parameter stays inside the finite-head bias radius.
    constructor
    · exact hδPos
    · calc
        δ ≤ uBias / 2 := by
          dsimp [δ]
          exact min_le_left _ _
        _ < uBias := by
          linarith
  have hδNorm : δ ∈ Set.Ioo 0 uNorm := by
    -- The same parameter also stays inside the norm-product radius.
    constructor
    · exact hδPos
    · calc
        δ ≤ uNorm / 2 := by
          dsimp [δ]
          exact min_le_right _ _
        _ < uNorm := by
          linarith
  have hmap :
      K (x : H₁) = (g : H₂) := by
    -- Taking `x` to be the range pseudoinverse removes the transport term exactly.
    simpa [x] using map_partialPseudoInverseOnRange g
  have hBiasAll :
      ∀ j : S.Index, |w (αChoice δ) (S.singularValue j ^ 2) - 1| ≤ B := by
    intro j
    -- Finite singular length lets us ask for the bias bound on the whole index set at once.
    exact huBias hδBias j (by simp)
  have hheadRaw :
      ‖S.reconstructionFamily w h_bound (αChoice δ) (g : H₂) - pinv‖ ≤
        B * ‖pinv‖ := by
    -- With exact data and full finite support, only the uniform bias multiplier remains.
    simpa [pinv] using
      exactDataError_le_uniformBias
        S w h_bound g (αChoice δ) B hB0 hBiasAll
  have hBmul : B * ‖pinv‖ ≤ ε := by
    -- The fixed normalization `max ‖pinv‖ 1` makes the bias contribution at most `ε`.
    calc
      B * ‖pinv‖ ≤ B * max ‖pinv‖ 1 := by
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) hB0
      _ = (ε / max ‖pinv‖ 1) * max ‖pinv‖ 1 := by
        rfl
      _ = ε := by
        have hmax : max ‖pinv‖ 1 ≠ 0 := by
          have hmaxpos : 0 < max ‖pinv‖ 1 := by
            exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
          exact ne_of_gt hmaxpos
        simpa [B] using div_mul_cancel₀ ε hmax
  refine ⟨δ, hδPos, x, ?_, ?_, ?_, huNorm hδNorm⟩
  · -- The finite-length branch uses the exact range pseudoinverse,
    -- so the approximation error is zero.
    simpa [x, pinv] using hε.le
  · -- Applying the same reconstruction map to equal data yields no transport error.
    simp [hmap, hε.le]
  · -- The exact-data reconstruction error is controlled by the full finite-support bias bound.
    calc
      ‖S.reconstructionFamily w h_bound (αChoice δ) (K (x : H₁)) - (x : H₁)‖
          = ‖S.reconstructionFamily w h_bound (αChoice δ) (g : H₂) - pinv‖ := by
              simp [x, pinv, hmap]
      _ ≤ B * ‖pinv‖ := hheadRaw
      _ ≤ ε := hBmul

/-- Helper for Theorem 2.19: for a fixed canonical initial segment, the exact-data
reconstructions along `αChoice δ` converge to that same initial segment as `δ → 0⁺`. -/
theorem initialSegmentExactDataConverges
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (g : K.range) (h_length : S.length = ⊤) (N : ℕ) :
    Tendsto
      (fun δ ↦
        S.reconstructionFamily w h_bound (αChoice δ)
          (K (S.initialSegmentRangePseudoInverse g h_length N : H₁)))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (S.initialSegmentRangePseudoInverse g h_length N : H₁)) := by
  let xN : K.kerᗮ := S.initialSegmentRangePseudoInverse g h_length N
  let F : Finset S.Index := (Finset.range N).image (S.natIndex h_length)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let B : ℝ := ε / (2 * max ‖(xN : H₁)‖ 1)
  have hBpos : 0 < B := by
    -- Normalize the bias budget by `max ‖xN‖ 1` so the head error stays below `ε`.
    have hden : 0 < 2 * max ‖(xN : H₁)‖ 1 := by
      positivity
    exact div_pos hε hden
  obtain ⟨u, hu, huBias⟩ :=
    initialSegmentBiasRadius S w lα αChoice h_choice h_pointwise h_length N hBpos
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT hu) ?_
  intro δ hδ
  have hsupport :
      ∀ j ∉ F, S.rightBasis.repr xN j = 0 := by
    -- The canonical initial segment is supported on the first `N` `natIndex` modes only.
    simpa [F, xN] using S.initialSegmentRangePseudoInverse_support g h_length N
  have hBsupport :
      ∀ j ∈ F, |w (αChoice δ) (S.singularValue j ^ 2) - 1| ≤ B := by
    intro j hj
    rcases Finset.mem_image.1 hj with ⟨i, hi, rfl⟩
    -- Repackage the initial-segment bias radius as a supportwise estimate on `F`.
    exact huBias hδ i (Finset.mem_range.1 hi)
  have hhead :
      ‖S.reconstructionFamily w h_bound (αChoice δ) (K (xN : H₁)) - (xN : H₁)‖ ≤
        B * ‖(xN : H₁)‖ := by
    -- On exact data `K xN`, only the supported bias multipliers contribute to the error.
    simpa [F, xN] using
      finiteHeadReconstructionError_le_norm
        S w h_bound (αChoice δ) F xN hsupport B hBpos.le hBsupport
  have hmax : 0 < max ‖(xN : H₁)‖ 1 := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hBmul :
      B * ‖(xN : H₁)‖ < ε := by
    -- The `max ‖xN‖ 1` normalization turns the supported head estimate into an `ε`-bound.
    calc
      B * ‖(xN : H₁)‖ ≤ B * max ‖(xN : H₁)‖ 1 := by
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) hBpos.le
      _ = ε / 2 := by
        have hmax_ne : max ‖(xN : H₁)‖ 1 ≠ 0 := ne_of_gt hmax
        dsimp [B]
        field_simp [hmax_ne]
      _ < ε := by
        linarith
  -- The supported head estimate is eventually smaller than the target ball radius.
  simpa [dist_eq_norm] using lt_of_le_of_lt hhead hBmul

/-- Helper for Theorem 2.19: for a fixed canonical initial segment, one can choose a positive
parameter stage where both the exact-data head error and the norm-product term are below any
prescribed tolerance. -/
theorem existsInitialSegmentExactDataStage
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (h_length : S.length = ⊤) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0,
      ‖S.reconstructionFamily w h_bound (αChoice δ)
            (K (S.initialSegmentRangePseudoInverse g h_length N : H₁)) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ ε ∧
      ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ ≤ ε := by
  have hconv :=
    initialSegmentExactDataConverges
      S w h_bound lα αChoice h_choice h_pointwise g h_length N
  have hHeadEvent :
      {δ : ℝ |
          ‖S.reconstructionFamily w h_bound (αChoice δ)
                (K (S.initialSegmentRangePseudoInverse g h_length N : H₁)) -
              (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ < ε} ∈
        nhdsWithin 0 (Set.Ioi 0) := by
    -- Turn convergence of the fixed head into a concrete right-neighborhood head-error set.
    refine Filter.mem_of_superset (Metric.tendsto_nhds.1 hconv ε hε) ?_
    intro δ hδ
    simpa [dist_eq_norm] using hδ
  obtain ⟨uHead, huHeadPos, huHead⟩ :=
    exists_Ioo_subset_of_mem_nhdsWithin_zero hHeadEvent
  obtain ⟨uNorm, huNormPos, huNorm⟩ :=
    normProductRadius S w h_bound αChoice h_norm hε
  let δ : ℝ := min (uHead / 2) (uNorm / 2)
  have hδPos : 0 < δ := by
    -- Halving both admissible radii keeps the selected stage positive.
    dsimp [δ]
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hδHead : δ ∈ Set.Ioo 0 uHead := by
    -- The selected stage lies inside the head-error neighborhood.
    constructor
    · exact hδPos
    · calc
        δ ≤ uHead / 2 := by
          dsimp [δ]
          exact min_le_left _ _
        _ < uHead := by
          linarith
  have hδNorm : δ ∈ Set.Ioo 0 uNorm := by
    -- The same stage also lies inside the norm-product neighborhood.
    constructor
    · exact hδPos
    · calc
        δ ≤ uNorm / 2 := by
          dsimp [δ]
          exact min_le_right _ _
        _ < uNorm := by
          linarith
  refine ⟨δ, hδPos, ?_, huNorm hδNorm⟩
  -- Combine the head-error neighborhood with the norm-product neighborhood at the same stage.
  exact (huHead hδHead).le

/-- Helper for Theorem 2.19: for a fixed canonical initial segment, the exact-data head error and
the norm-product bound hold uniformly on a whole right-neighborhood interval `(0, u)`. -/
theorem existsInitialSegmentExactDataWindow
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (h_length : S.length = ⊤) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u > 0, ∀ ⦃δ : ℝ⦄, δ ∈ Set.Ioo 0 u →
      ‖S.reconstructionFamily w h_bound (αChoice δ)
            (K (S.initialSegmentRangePseudoInverse g h_length N : H₁)) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ ε ∧
      ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ ≤ ε := by
  have hconv :=
    initialSegmentExactDataConverges
      S w h_bound lα αChoice h_choice h_pointwise g h_length N
  have hHeadEvent :
      {δ : ℝ |
          ‖S.reconstructionFamily w h_bound (αChoice δ)
                (K (S.initialSegmentRangePseudoInverse g h_length N : H₁)) -
              (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ < ε} ∈
        nhdsWithin 0 (Set.Ioi 0) := by
    -- Recast exact-data convergence of the fixed head as an interval-valued neighborhood.
    refine Filter.mem_of_superset (Metric.tendsto_nhds.1 hconv ε hε) ?_
    intro δ hδ
    simpa [dist_eq_norm] using hδ
  obtain ⟨uHead, huHeadPos, huHead⟩ :=
    exists_Ioo_subset_of_mem_nhdsWithin_zero hHeadEvent
  obtain ⟨uNorm, huNormPos, huNorm⟩ :=
    normProductRadius S w h_bound αChoice h_norm hε
  refine ⟨min uHead uNorm, lt_min huHeadPos huNormPos, ?_⟩
  intro δ hδ
  have hδHead : δ ∈ Set.Ioo 0 uHead := by
    refine ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩
  have hδNorm : δ ∈ Set.Ioo 0 uNorm := by
    refine ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_right _ _)⟩
  -- Both interval constraints now hold at the same parameter `δ`.
  exact ⟨(huHead hδHead).le, huNorm hδNorm⟩
omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Helper for Theorem 2.19: the buffered radii
`‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n` stay in `Set.Ioi 0` and converge to `0`. -/
theorem bufferedDatumError_tendstoWithin
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂))) :
    let δSeq : ℕ → ℝ := fun n ↦ ‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n
    Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  let δSeq : ℕ → ℝ := fun n ↦ ‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n
  have hErr :
      Tendsto (fun n ↦ ‖gSeq n - (g : H₂)‖) atTop (𝓝 0) := by
    -- The datum error tends to `0` because `gSeq` converges to the exact datum `g`.
    have hgConst : Tendsto (fun _ : ℕ ↦ (g : H₂)) atTop (𝓝 (g : H₂)) := tendsto_const_nhds
    have hSub : Tendsto (fun n ↦ gSeq n - (g : H₂)) atTop (𝓝 (0 : H₂)) := by
      simpa using hgSeq.sub hgConst
    simpa using Tendsto.norm hSub
  have hPow :
      Tendsto (fun n : ℕ ↦ (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    -- The geometric buffer keeps the radii strictly positive while still vanishing.
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hδ :
      Tendsto δSeq atTop (𝓝 0) := by
    -- The buffered radii are the sum of the datum error and a vanishing positive buffer.
    simpa [δSeq] using hErr.add hPow
  have hδpos : ∀ᶠ n : ℕ in atTop, δSeq n ∈ Set.Ioi 0 := by
    -- Every buffered radius is positive because the geometric buffer is positive.
    exact Filter.Eventually.of_forall fun n ↦ by
      change 0 < δSeq n
      have hpowPos : 0 < (1 / 4 : ℝ) ^ n := by
        positivity
      simpa [δSeq] using
        add_pos_of_nonneg_of_pos (norm_nonneg (gSeq n - (g : H₂))) hpowPos
  simpa [δSeq] using
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within δSeq hδ hδpos

/-- Helper for Theorem 2.19: choosing the parameter from the buffered datum-error sequence makes
the purely noisy perturbation term converge to `0`. -/
theorem bufferedChoiceNoiseBound_tendstoZero
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂))) :
    let δSeq : ℕ → ℝ := fun n ↦ ‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n
    Tendsto
      (fun n ↦
        ‖S.reconstructionFamily w h_bound (αChoice (δSeq n)) (gSeq n) -
            S.reconstructionFamily w h_bound (αChoice (δSeq n)) (g : H₂)‖)
      atTop (𝓝 0) := by
  let δSeq : ℕ → ℝ := fun n ↦ ‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n
  have hδ :
      Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    -- Reuse the buffered-radius package so the norm-product hypothesis can be composed directly.
    simpa [δSeq] using
      bufferedDatumError_tendstoWithin g gSeq hgSeq
  have hprod :
      Tendsto
        (fun n ↦ ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * δSeq n)
        atTop (𝓝 0) := by
    -- Compose the norm-product hypothesis with the buffered radii.
    change
      Tendsto
        ((fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ) ∘ δSeq)
        atTop (𝓝 0)
    exact h_norm.comp hδ
  have hbound :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δSeq n)) (gSeq n) -
            S.reconstructionFamily w h_bound (αChoice (δSeq n)) (g : H₂)‖ ≤
          ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * δSeq n := by
    intro n
    -- The buffered radius dominates the true datum error, so the operator-norm estimate applies.
    calc
      ‖S.reconstructionFamily w h_bound (αChoice (δSeq n)) (gSeq n) -
          S.reconstructionFamily w h_bound (αChoice (δSeq n)) (g : H₂)‖
          ≤ ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * ‖gSeq n - (g : H₂)‖ := by
            simpa using
              reconstructionFamily_apply_sub_le
                S w h_bound (αChoice (δSeq n)) (gSeq n) (g : H₂)
      _ ≤ ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * δSeq n := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            dsimp [δSeq]
            exact le_add_of_nonneg_right (by positivity)
  simpa [δSeq] using
    squeeze_zero
      (fun n ↦ norm_nonneg _)
      hbound
      hprod

/-- Helper for Theorem 2.19: when the singular system has finite length, the exact-data
reconstructions already converge along the raw buffered choice
`δBuf n = ‖gSeq n - g‖ + (1 / 4)^n`. -/
theorem finiteLengthExactDataConvergesAlongBufferedChoice
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂)))
    (h_length : S.length ≠ ⊤) :
    let δBuf : ℕ → ℝ := fun n ↦ ‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n
    Tendsto
      (fun n ↦
        S.reconstructionFamily w h_bound (αChoice (δBuf n)) (g : H₂))
      atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  classical
  haveI : Finite S.Index := S.finiteIndexOfLengthNeTop h_length
  letI : Fintype S.Index := Fintype.ofFinite S.Index
  let δBuf : ℕ → ℝ := fun n ↦ ‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n
  let pinv : H₁ := (K.kerOrthogonalEquivRange.symm g : H₁)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let B : ℝ := ε / (2 * max ‖pinv‖ 1)
  have hBpos : 0 < B := by
    -- The finite-length branch uses a fixed positive bias budget on the whole singular support.
    have hden : 0 < 2 * max ‖pinv‖ 1 := by
      positivity
    exact div_pos hε hden
  have hδ :
      Tendsto δBuf atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    -- The raw buffered radii still converge to `0` through positive parameters.
    simpa [δBuf] using
      bufferedDatumError_tendstoWithin g gSeq hgSeq
  have hBias :
      ∀ᶠ n in atTop,
        ∀ j : S.Index, |w (αChoice (δBuf n)) (S.singularValue j ^ 2) - 1| ≤ B := by
    -- Finite singular length lets us ask for the bias bound on all modes at once.
    simpa [δBuf] using
      finiteHeadBiasAlongChoiceSequence
        S w lα αChoice h_choice h_pointwise Finset.univ hBpos δBuf hδ
  have hBmul :
      B * ‖pinv‖ < ε := by
    -- The `max ‖pinv‖ 1` normalization turns the uniform bias bound into an `ε`-estimate.
    calc
      B * ‖pinv‖ ≤ B * max ‖pinv‖ 1 := by
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) hBpos.le
      _ = ε / 2 := by
        have hmax : max ‖pinv‖ 1 ≠ 0 := by
          have hmaxPos : 0 < max ‖pinv‖ 1 := by
            exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
          exact ne_of_gt hmaxPos
        dsimp [B]
        field_simp [hmax]
      _ < ε := by
        linarith
  rcases Filter.mem_atTop_sets.1 hBias with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have hBiasAll :
      ∀ j : S.Index, |w (αChoice (δBuf n)) (S.singularValue j ^ 2) - 1| ≤ B := by
    intro j
    exact hN n hn j
  have hErr :
      ‖S.reconstructionFamily w h_bound (αChoice (δBuf n)) (g : H₂) - pinv‖ ≤
        B * ‖pinv‖ := by
    -- On exact data, the finite singular support reduces the error to the uniform bias budget.
    simpa [pinv] using
      exactDataError_le_uniformBias
        S w h_bound g (αChoice (δBuf n)) B hBpos.le hBiasAll
  calc
    dist
        (S.reconstructionFamily w h_bound (αChoice (δBuf n)) (g : H₂))
        pinv =
        ‖S.reconstructionFamily w h_bound (αChoice (δBuf n)) (g : H₂) - pinv‖ := by
          rw [dist_eq_norm]
    _ ≤ B * ‖pinv‖ := hErr
    _ < ε := hBmul

omit [InnerProductSpace ℝ H₂] [CompleteSpace H₂] in
/-- Helper for Theorem 2.19: every positive error schedule can be matched by a strictly
increasing tail cutoff along a convergent datum sequence. -/
theorem existsIncreasingTailCutoff
    {g : H₂} (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 g))
    (δStage : ℕ → ℝ)
    (hδStagePos : ∀ n, 0 < δStage n) :
    ∃ cut : ℕ → ℕ, StrictMono cut ∧
      ∀ n, ∀ k ≥ cut n, ‖gSeq k - g‖ ≤ δStage n := by
  classical
  have htail :
      ∀ n m : ℕ,
        ∃ N : ℕ, m < N ∧ ∀ k ≥ N, ‖gSeq k - g‖ ≤ δStage n := by
    intro n m
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hgSeq (δStage n) (hδStagePos n)
    refine ⟨max N (m + 1), ?_, ?_⟩
    · -- Stepping past `m` at each stage will make the recursive cutoff strictly increasing.
      exact lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right N (m + 1))
    · intro k hk
      have hkN : N ≤ k := le_trans (Nat.le_max_left N (m + 1)) hk
      -- Once `k` is beyond the chosen tail threshold, the datum error lies inside the stage ball.
      simpa [dist_eq_norm] using (hN k hkN).le
  let cut : ℕ → ℕ :=
    Nat.rec
      (Classical.choose (htail 0 0))
      (fun n prev ↦ Classical.choose (htail (n + 1) prev))
  have hcut_step : ∀ n, cut n < cut (n + 1) := by
    intro n
    induction n with
    | zero =>
        -- Unfold the first recursive step to read the strict tail advance from `htail`.
        simpa [cut] using (Classical.choose_spec (htail 1 (cut 0))).1
    | succ n ih =>
        -- Every later step uses the previous cutoff as the lower bound for the next tail.
        simpa [cut] using (Classical.choose_spec (htail (n + 2) (cut (n + 1)))).1
  have hcut_tail :
      ∀ n, ∀ k ≥ cut n, ‖gSeq k - g‖ ≤ δStage n := by
    intro n
    induction n with
    | zero =>
        -- The initial cutoff is chosen from the first tail witness for `δStage 0`.
        simpa [cut] using (Classical.choose_spec (htail 0 0)).2
    | succ n ih =>
        -- Each recursive cutoff carries the required tail estimate for the next stage radius.
        simpa [cut] using (Classical.choose_spec (htail (n + 1) (cut n))).2
  refine ⟨cut, strictMono_nat_of_lt_succ hcut_step, hcut_tail⟩

/-- Helper for Theorem 2.19: once one stage radius dominates both the exact-data defect and the
tail of the noisy datum sequence, the operator-norm estimate gives the whole noisy block bound. -/
theorem noiseBlockBoundFromStageRadius
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (gSeq : ℕ → H₂) (α : ι) (δ : ℝ) (x : K.kerᗮ) (cut : ℕ) {ε : ℝ}
    (_hδPos : 0 < δ)
    (hdata : ‖(g : H₂) - K (x : H₁)‖ ≤ δ / 2)
    (hcut :
      ∀ k ≥ cut, ‖gSeq k - (g : H₂)‖ ≤ δ / 2)
    (hnorm :
      ‖S.reconstructionFamily w h_bound α‖ * δ ≤ ε) :
    ∀ k ≥ cut,
      ‖S.reconstructionFamily w h_bound α (gSeq k) -
          S.reconstructionFamily w h_bound α (K (x : H₁))‖ ≤
        ε := by
  intro k hk
  -- First collapse the datum mismatch to the single radius `δ` by a triangle inequality.
  have hdatum :
      ‖gSeq k - K (x : H₁)‖ ≤ δ := by
    have hdecomp :
        gSeq k - K (x : H₁) =
          (gSeq k - (g : H₂)) + ((g : H₂) - K (x : H₁)) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
      abel_nf
    rw [hdecomp]
    calc
      ‖(gSeq k - (g : H₂)) + ((g : H₂) - K (x : H₁))‖
          ≤ ‖gSeq k - (g : H₂)‖ + ‖(g : H₂) - K (x : H₁)‖ := norm_add_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add (hcut k hk) hdata
      _ = δ := by ring
  -- Then feed that datum bound into the operator-norm estimate at the chosen stage.
  calc
    ‖S.reconstructionFamily w h_bound α (gSeq k) -
        S.reconstructionFamily w h_bound α (K (x : H₁))‖
        ≤ ‖S.reconstructionFamily w h_bound α‖ * ‖gSeq k - K (x : H₁)‖ := by
          simpa using
            reconstructionFamily_apply_sub_le
              S w h_bound α (gSeq k) (K (x : H₁))
    _ ≤ ‖S.reconstructionFamily w h_bound α‖ * δ := by
          exact mul_le_mul_of_nonneg_left hdatum (norm_nonneg _)
    _ ≤ ε := hnorm

/-- Helper for Theorem 2.19: exact-data control can be transferred from one `K.kerᗮ` head to
another at the same stage by paying only for their two datum defects and their ambient
distance. -/
theorem exactDataHeadTransferFromDatum
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (α : ι) (xCore xStage : K.kerᗮ) :
    ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖ ≤
      ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
        ‖S.reconstructionFamily w h_bound α‖ *
          (‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖) +
        ‖(xStage : H₁) - (xCore : H₁)‖ := by
  let Rα := S.reconstructionFamily w h_bound α
  have hsplit :
      Rα (K (xStage : H₁)) - (xStage : H₁) =
        (Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))) +
          ((Rα (K (xCore : H₁)) - (xCore : H₁)) +
            ((xCore : H₁) - (xStage : H₁))) := by
    -- Split the later-head error into transport, core exact-data error, and head mismatch.
    simp [Rα, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hKdiff :
      ‖K (xStage : H₁) - K (xCore : H₁)‖ ≤
        ‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖ := by
    have hdecomp :
        K (xStage : H₁) - K (xCore : H₁) =
          (K (xStage : H₁) - (g : H₂)) + ((g : H₂) - K (xCore : H₁)) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hdecomp]
    calc
      ‖(K (xStage : H₁) - (g : H₂)) + ((g : H₂) - K (xCore : H₁))‖
          ≤ ‖K (xStage : H₁) - (g : H₂)‖ + ‖(g : H₂) - K (xCore : H₁)‖ := by
            exact norm_add_le _ _
      _ = ‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖ := by
            rw [norm_sub_rev]
  have htransport :
      ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ ≤
        ‖Rα‖ *
          (‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖) := by
    calc
      ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖
          ≤ ‖Rα‖ * ‖K (xStage : H₁) - K (xCore : H₁)‖ := by
            simpa [Rα] using
              reconstructionFamily_apply_sub_le
                S w h_bound α (K (xStage : H₁)) (K (xCore : H₁))
      _ ≤ ‖Rα‖ *
          (‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖) := by
            exact mul_le_mul_of_nonneg_left hKdiff (norm_nonneg _)
  -- Combine the transport estimate with the core exact-data error and the ambient head mismatch.
  rw [hsplit]
  calc
    ‖(Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))) +
        ((Rα (K (xCore : H₁)) - (xCore : H₁)) + ((xCore : H₁) - (xStage : H₁)))‖
        ≤ ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ +
            ‖(Rα (K (xCore : H₁)) - (xCore : H₁)) + ((xCore : H₁) - (xStage : H₁))‖ := by
          exact norm_add_le _ _
    _ ≤ ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ +
          (‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ + ‖(xCore : H₁) - (xStage : H₁)‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
          ‖S.reconstructionFamily w h_bound α‖ *
            (‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖) +
          ‖(xStage : H₁) - (xCore : H₁)‖ := by
          have hdist :
              ‖(xCore : H₁) - (xStage : H₁)‖ = ‖(xStage : H₁) - (xCore : H₁)‖ := by
            rw [norm_sub_rev]
          calc
            ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ +
                (‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ +
                  ‖(xCore : H₁) - (xStage : H₁)‖)
                ≤ ‖Rα‖ *
                    (‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖) +
                    (‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ +
                      ‖(xCore : H₁) - (xStage : H₁)‖) := by
                  exact add_le_add_left htransport _
            _ = ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
                  ‖S.reconstructionFamily w h_bound α‖ *
                    (‖(g : H₂) - K (xStage : H₁)‖ + ‖(g : H₂) - K (xCore : H₁)‖) +
                  ‖(xStage : H₁) - (xCore : H₁)‖ := by
                  rw [hdist]
                  ring

/-- Helper for Theorem 2.19: once the stage is fixed, moving from one exact-data head to another
only costs the transported datum difference and the ambient head displacement. -/
theorem exactDataHeadTransferFromDistance
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (xCore xStage : K.kerᗮ) :
    ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖ ≤
      ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
        ‖S.reconstructionFamily w h_bound α‖ * ‖K ((xStage : H₁) - (xCore : H₁))‖ +
        ‖(xStage : H₁) - (xCore : H₁)‖ := by
  let Rα := S.reconstructionFamily w h_bound α
  have hsplit :
      Rα (K (xStage : H₁)) - (xStage : H₁) =
        (Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))) +
          ((Rα (K (xCore : H₁)) - (xCore : H₁)) +
            ((xCore : H₁) - (xStage : H₁))) := by
    -- Split the later-head exact-data error into transport, the core head error, and the
    -- ambient displacement between the two heads.
    simp [Rα, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have htransport :
      ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ ≤
        ‖Rα‖ * ‖K ((xStage : H₁) - (xCore : H₁))‖ := by
    calc
      ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖
          ≤ ‖Rα‖ * ‖K (xStage : H₁) - K (xCore : H₁)‖ := by
            simpa [Rα] using
              reconstructionFamily_apply_sub_le
                S w h_bound α (K (xStage : H₁)) (K (xCore : H₁))
      _ = ‖Rα‖ * ‖K ((xStage : H₁) - (xCore : H₁))‖ := by
            rw [ContinuousLinearMap.map_sub]
  -- Combine the fixed-stage transport estimate with the core exact-data error.
  rw [hsplit]
  calc
    ‖(Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))) +
        ((Rα (K (xCore : H₁)) - (xCore : H₁)) + ((xCore : H₁) - (xStage : H₁)))‖
        ≤ ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ +
            ‖(Rα (K (xCore : H₁)) - (xCore : H₁)) + ((xCore : H₁) - (xStage : H₁))‖ := by
          exact norm_add_le _ _
    _ ≤ ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ +
          (‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ + ‖(xCore : H₁) - (xStage : H₁)‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
          ‖S.reconstructionFamily w h_bound α‖ * ‖K ((xStage : H₁) - (xCore : H₁))‖ +
          ‖(xStage : H₁) - (xCore : H₁)‖ := by
          have hdist :
              ‖(xCore : H₁) - (xStage : H₁)‖ = ‖(xStage : H₁) - (xCore : H₁)‖ := by
            rw [norm_sub_rev]
          calc
            ‖Rα (K (xStage : H₁)) - Rα (K (xCore : H₁))‖ +
                (‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ +
                  ‖(xCore : H₁) - (xStage : H₁)‖)
                ≤ ‖Rα‖ * ‖K ((xStage : H₁) - (xCore : H₁))‖ +
                    (‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ +
                      ‖(xCore : H₁) - (xStage : H₁)‖) := by
                  exact add_le_add_left htransport _
            _ = ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
                  ‖S.reconstructionFamily w h_bound α‖ * ‖K ((xStage : H₁) - (xCore : H₁))‖ +
                  ‖(xStage : H₁) - (xCore : H₁)‖ := by
                  rw [hdist]
                  ring

/-- Helper for Theorem 2.19: after rewriting the transported datum term through the operator
norm of `K`, the fixed-stage exact-data transfer estimate depends only on the ambient distance
between the two heads. -/
theorem stageTransportDistanceBound
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (xCore xStage : K.kerᗮ) :
    ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖ ≤
      ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
        (‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1) *
          ‖(xStage : H₁) - (xCore : H₁)‖ := by
  let Rα := S.reconstructionFamily w h_bound α
  have hK :
      ‖K ((xStage : H₁) - (xCore : H₁))‖ ≤
        ‖K‖ * ‖(xStage : H₁) - (xCore : H₁)‖ := by
    -- Bound the transported head displacement by the operator norm of `K`.
    exact K.le_opNorm ((xStage : H₁) - (xCore : H₁))
  -- Replace the `K`-transport term in the exact-data transfer estimate by the ambient distance.
  calc
    ‖Rα (K (xStage : H₁)) - (xStage : H₁)‖
        ≤ ‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ +
            ‖Rα‖ * ‖K ((xStage : H₁) - (xCore : H₁))‖ +
            ‖(xStage : H₁) - (xCore : H₁)‖ := by
          simpa [Rα] using
            exactDataHeadTransferFromDistance
              S w h_bound α xCore xStage
    _ ≤ ‖Rα (K (xCore : H₁)) - (xCore : H₁)‖ +
          ‖Rα‖ * (‖K‖ * ‖(xStage : H₁) - (xCore : H₁)‖) +
            ‖(xStage : H₁) - (xCore : H₁)‖ := by
          gcongr
    _ = ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
          (‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1) *
            ‖(xStage : H₁) - (xCore : H₁)‖ := by
          ring

/-- Helper for Theorem 2.19: once a stage `α` and a radius `δCore` are fixed, a later canonical
initial segment can be chosen to satisfy both the datum cutoff `δCore / 2` and the normalized
approximation budget for that same fixed stage. -/
theorem existsLaterInitialSegmentForFixedStage
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (h_length : S.length = ⊤)
    (α : ι) (n : ℕ) (δCore : ℝ) (hδCorePos : 0 < δCore) (NMin : ℕ) :
    ∃ N ≥ NMin,
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n /
          (8 * (‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1)) ∧
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤
        δCore / 2 ∧
      ‖(g : H₂) - K (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤
        δCore / 2 := by
  let ηApprox : ℝ :=
    min
      ((1 / 4 : ℝ) ^ n /
        (8 * (‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1)))
      (δCore / 2)
  have hηApproxPos : 0 < ηApprox := by
    -- Both the normalized approximation budget and the datum cutoff are positive.
    dsimp [ηApprox]
    refine lt_min ?_ ?_
    · positivity
    · linarith
  obtain ⟨N0, hN0⟩ :=
    initialSegmentRangePseudoInverseApproxEventually
      S g h_length (η := ηApprox) hηApproxPos
  let N := max N0 NMin
  have hNNow := hN0 N (le_max_left _ _)
  refine ⟨N, le_max_right _ _, ?_, ?_, ?_⟩
  · -- The chosen later head satisfies the fixed-stage normalized approximation budget.
    exact le_trans hNNow.1 (min_le_left _ _)
  · -- The same approximation estimate also lies inside the datum cutoff radius.
    exact le_trans hNNow.1 (min_le_right _ _)
  · -- The exact datum of the later head is already inside the required `δCore / 2` ball.
    exact le_trans hNNow.2 (min_le_right _ _)

/-- Helper for Theorem 2.19: for one geometric tolerance `(1 / 4)^n`, one can already choose a
single canonical exact-data stage that controls a core head and the norm product. -/
theorem existsInfiniteLengthExactDataRadius
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (h_length : S.length = ⊤) (n : ℕ) :
    ∃ δStage > 0, ∃ NStage : ℕ,
      let xStage : K.kerᗮ := S.initialSegmentRangePseudoInverse g h_length NStage
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xStage : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n / 8 ∧
        ‖S.reconstructionFamily w h_bound (αChoice δStage) (K (xStage : H₁)) -
            (xStage : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n / 4 ∧
        ‖S.reconstructionFamily w h_bound (αChoice δStage)‖ * δStage ≤
          (1 / 4 : ℝ) ^ n / 4 := by
  have happroxScale : 0 < (1 / 4 : ℝ) ^ n / 8 := by
    positivity
  obtain ⟨N0, hN0⟩ :=
    initialSegmentRangePseudoInverseApproxEventually
      S g h_length (η := (1 / 4 : ℝ) ^ n / 8) happroxScale
  have happrox0 :
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) -
          (S.initialSegmentRangePseudoInverse g h_length N0 : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 8 := by
    -- Freeze one canonical core head with the target geometric approximation budget.
    exact (hN0 N0 le_rfl).1
  have hheadScale : 0 < (1 / 4 : ℝ) ^ n / 4 := by
    positivity
  obtain ⟨δStage, hδStagePos, hhead, hnormStage⟩ :=
    existsInitialSegmentExactDataStage
      S w h_bound lα αChoice h_choice h_pointwise h_norm g h_length N0 hheadScale
  refine ⟨δStage, hδStagePos, N0, ?_, ?_, ?_⟩
  · -- The chosen core stage inherits the canonical initial-segment approximation estimate.
    simpa using happrox0
  · -- The exact-data head control comes from the one-stage initial-segment theorem.
    simpa using hhead
  · -- The same stage also satisfies the required norm-product bound.
    simpa using hnormStage

/-- Helper for Theorem 2.19: any positive-null schedule admits a strict subsequence along which
the norm product already obeys the geometric budget required by the infinite branch. -/
theorem existsNormControlledSubsequenceAlongChoice
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (δSeq : ℕ → ℝ)
    (hδSeq : Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0))) :
    ∃ stageOf : ℕ → ℕ, StrictMono stageOf ∧
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δSeq (stageOf n)))‖ *
            δSeq (stageOf n) ≤
          (1 / 4 : ℝ) ^ n / 4 := by
  let prodSeq : ℕ → ℝ := fun n ↦
    ‖S.reconstructionFamily w h_bound (αChoice (δSeq n))‖ * δSeq n
  have hprod : Tendsto prodSeq atTop (𝓝 0) := by
    -- Compose the neighborhood norm-product hypothesis with the concrete positive-null schedule.
    change
      Tendsto
        ((fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ) ∘ δSeq)
        atTop (𝓝 0)
    simpa [Function.comp, prodSeq] using h_norm.comp hδSeq
  have htail :
      ∀ n m : ℕ, ∃ N : ℕ, m < N ∧
        ∀ k ≥ N, prodSeq k ≤ (1 / 4 : ℝ) ^ n / 4 := by
    intro n m
    have hε : 0 < (1 / 4 : ℝ) ^ n / 4 := by
      positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hprod ((1 / 4 : ℝ) ^ n / 4) hε
    refine ⟨max N (m + 1), ?_, ?_⟩
    · -- Stepping past `m` at each stage makes the chosen selector strictly increasing.
      exact lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right N (m + 1))
    · intro k hk
      have hkN : N ≤ k := le_trans (Nat.le_max_left N (m + 1)) hk
      have habs : |prodSeq k| < (1 / 4 : ℝ) ^ n / 4 := by
        -- The tail of the composed norm product already lies in the target `ε`-ball.
        simpa [prodSeq, Real.dist_eq] using hN k hkN
      exact le_trans (le_abs_self _) habs.le
  let stageOf : ℕ → ℕ :=
    Nat.rec
      (Classical.choose (htail 0 0))
      (fun n prev ↦ Classical.choose (htail (n + 1) prev))
  have hstageStep : ∀ n, stageOf n < stageOf (n + 1) := by
    intro n
    induction n with
    | zero =>
        -- The first recursive step starts strictly after the base stage.
        simpa [stageOf] using (Classical.choose_spec (htail 1 (stageOf 0))).1
    | succ n ih =>
        -- Every later recursive step starts strictly after the previous chosen stage.
        simpa [stageOf] using (Classical.choose_spec (htail (n + 2) (stageOf (n + 1)))).1
  have hstageNorm :
      ∀ n, prodSeq (stageOf n) ≤ (1 / 4 : ℝ) ^ n / 4 := by
    intro n
    induction n with
    | zero =>
        -- The base stage already satisfies the zeroth geometric norm-product budget.
        exact (Classical.choose_spec (htail 0 0)).2 _ le_rfl
    | succ n ih =>
        -- Each recursive stage inherits the corresponding geometric norm-product estimate.
        exact (Classical.choose_spec (htail (n + 1) (stageOf n))).2 _ le_rfl
  refine ⟨stageOf, strictMono_nat_of_lt_succ hstageStep, ?_⟩
  intro n
  -- Unfold the packaged sequence notation and read off the stored stage estimate.
  simpa [prodSeq] using hstageNorm n

/-- Helper for Theorem 2.19: every positive-null schedule still hits any prescribed right
neighborhood of `0` after any finite cutoff. -/
theorem existsLaterScheduleIndexInWindow
    (δSeq : ℕ → ℝ)
    (hδSeq : Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0)))
    (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∃ k > m, δSeq k ∈ Set.Ioo 0 u := by
  have hwindow : ∀ᶠ k : ℕ in atTop, δSeq k ∈ Set.Ioo 0 u := by
    -- Compose the positive-null schedule with the standard right-neighborhood interval at `0`.
    exact hδSeq.eventually (Ioo_mem_nhdsGT hu)
  rcases Filter.mem_atTop_sets.1 hwindow with ⟨N, hN⟩
  refine ⟨max N (m + 1), ?_, ?_⟩
  · -- Choosing the maximum with `m + 1` forces the later schedule index to lie past `m`.
    exact lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right N (m + 1))
  · -- The chosen stage is still inside the prescribed right-neighborhood interval.
    exact hN _ (Nat.le_max_left N (m + 1))

/-- Helper for Theorem 2.19: after any cutoff, one can still find a later schedule stage whose
norm product satisfies the geometric budget required for the infinite exact-data branch. -/
theorem existsLaterNormControlledStage
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (δSeq : ℕ → ℝ)
    (hδSeq : Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0)))
    (m n : ℕ) :
    ∃ k > m,
      ‖S.reconstructionFamily w h_bound (αChoice (δSeq k))‖ * δSeq k ≤
        (1 / 4 : ℝ) ^ n / 4 := by
  have hε : 0 < (1 / 4 : ℝ) ^ n / 4 := by
    positivity
  obtain ⟨u, huPos, huNorm⟩ :=
    normProductRadius S w h_bound αChoice h_norm hε
  obtain ⟨k, hk, hkWindow⟩ :=
    existsLaterScheduleIndexInWindow δSeq hδSeq m huPos
  refine ⟨k, hk, ?_⟩
  -- The stage chosen inside the norm-product window inherits the required geometric bound.
  exact huNorm hkWindow

/-- Helper for Theorem 2.19: after any cutoff, a fixed canonical initial segment still appears at
a later schedule stage where both its exact-data head error and the norm product lie below the
same prescribed tolerance. -/
theorem existsLaterScheduleStageForInitialSegmentWindow
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (h_length : S.length = ⊤)
    (δSeq : ℕ → ℝ)
    (hδSeq : Tendsto δSeq atTop (nhdsWithin 0 (Set.Ioi 0)))
    (N m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k > m,
      0 < δSeq k ∧
      ‖S.reconstructionFamily w h_bound (αChoice (δSeq k))
            (K (S.initialSegmentRangePseudoInverse g h_length N : H₁)) -
          (S.initialSegmentRangePseudoInverse g h_length N : H₁)‖ ≤ ε ∧
      ‖S.reconstructionFamily w h_bound (αChoice (δSeq k))‖ * δSeq k ≤ ε := by
  obtain ⟨u, huPos, huWindow⟩ :=
    existsInitialSegmentExactDataWindow
      S w h_bound lα αChoice h_choice h_pointwise h_norm g h_length N hε
  obtain ⟨k, hk, hkWindow⟩ :=
    existsLaterScheduleIndexInWindow δSeq hδSeq m huPos
  refine ⟨k, hk, hkWindow.1, ?_, ?_⟩
  · -- Evaluate the fixed-head neighborhood bounds at the chosen later schedule index.
    exact (huWindow hkWindow).1
  · -- The same schedule index inherits the norm-product bound from the common window.
    exact (huWindow hkWindow).2

/-- Helper for Theorem 2.19: once a filter stage `α` is fixed, continuity of the corresponding
reconstruction operator turns `gSeq → g` into a uniform tail cutoff for that stage. -/
theorem existsFixedOperatorTailCutoff
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂)))
    (α : ι) (m n : ℕ) :
    ∃ cut > m,
      ∀ k ≥ cut,
        ‖S.reconstructionFamily w h_bound α (gSeq k) -
            S.reconstructionFamily w h_bound α (g : H₂)‖ ≤
          (1 / 4 : ℝ) ^ n / 2 := by
  let Rα := S.reconstructionFamily w h_bound α
  have hε : 0 < (1 / 4 : ℝ) ^ n / 2 := by
    positivity
  have hcomp :
      Tendsto ((fun x : H₂ ↦ Rα x) ∘ gSeq) atTop (𝓝 (Rα (g : H₂))) := by
    -- Route correction: after fixing `α`, the noisy tail is handled by ordinary continuity
    -- instead of another stage-radius compatibility search.
    exact Rα.continuous.continuousAt.tendsto.comp hgSeq
  obtain ⟨cut0, hcut0⟩ := Metric.tendsto_atTop.1 hcomp ((1 / 4 : ℝ) ^ n / 2) hε
  refine ⟨max cut0 (m + 1), ?_, ?_⟩
  · -- Taking the maximum with `m + 1` preserves the continuity cutoff while forcing `cut > m`.
    exact lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right cut0 (m + 1))
  · intro k hk
    have hk0 : cut0 ≤ k := le_trans (Nat.le_max_left cut0 (m + 1)) hk
    -- Beyond the chosen cutoff, every noisy datum lies inside the fixed operator ball.
    simpa [dist_eq_norm, Rα] using (hcut0 k hk0).le

/-- Helper for Theorem 2.19: a fixed reconstruction operator admits an explicit datum radius on
which the transport to the exact datum is bounded by any prescribed tolerance. -/
theorem fixedOperatorDatumRadius
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (g : K.range) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ y : H₂, ‖y - (g : H₂)‖ ≤ ρ →
      ‖S.reconstructionFamily w h_bound α y -
          S.reconstructionFamily w h_bound α (g : H₂)‖ ≤ ε := by
  let Rα := S.reconstructionFamily w h_bound α
  let ρ : ℝ := ε / (‖Rα‖ + 1)
  have hρPos : 0 < ρ := by
    -- The explicit operator-norm radius is positive because `ε > 0` and `‖Rα‖ + 1 > 0`.
    dsimp [ρ]
    positivity
  refine ⟨ρ, hρPos, ?_⟩
  intro y hy
  have hratio : ‖Rα‖ / (‖Rα‖ + 1) ≤ (1 : ℝ) := by
    have hdenPos : 0 < ‖Rα‖ + 1 := by
      positivity
    have hdenNe : ‖Rα‖ + 1 ≠ 0 := ne_of_gt hdenPos
    have hrecipNonneg : 0 ≤ 1 / (‖Rα‖ + 1) := by
      positivity
    -- Rewrite the ratio as `1 - 1 / (‖Rα‖ + 1)` to compare directly with `1`.
    calc
      ‖Rα‖ / (‖Rα‖ + 1) = 1 - 1 / (‖Rα‖ + 1) := by
        field_simp [hdenNe]
        ring
      _ ≤ 1 := by
        linarith
  calc
    ‖S.reconstructionFamily w h_bound α y -
        S.reconstructionFamily w h_bound α (g : H₂)‖
        ≤ ‖Rα‖ * ‖y - (g : H₂)‖ := by
          simpa [Rα] using
            reconstructionFamily_apply_sub_le
              S w h_bound α y (g : H₂)
    _ ≤ ‖Rα‖ * ρ := by
          exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = ε * (‖Rα‖ / (‖Rα‖ + 1)) := by
          dsimp [ρ]
          ring
    _ ≤ ε * 1 := by
          exact mul_le_mul_of_nonneg_left hratio hε.le
    _ = ε := by
          ring

/-- Helper for Theorem 2.19: if a later head is within the fixed-stage transport scale of a core
head, then the core exact-data estimate transfers to the later head with the desired geometric
budget. -/
theorem laterInitialSegmentHeadBoundFromDistance
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (xCore xStage : K.kerᗮ) (n : ℕ)
    (hcore :
      ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 4)
    (hdist :
      ‖(xStage : H₁) - (xCore : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n /
          (4 * (‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1))) :
    ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖ ≤
      (1 / 4 : ℝ) ^ n / 2 := by
  let factor : ℝ := ‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1
  have hfactorPos : 0 < factor := by
    -- The transport factor is strictly positive because it is a nonnegative term plus `1`.
    dsimp [factor]
    positivity
  have htransport :
      ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖ ≤
        ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
          factor * ‖(xStage : H₁) - (xCore : H₁)‖ := by
    -- Rewrite the generic fixed-stage transfer estimate with the local transport factor name.
    simpa [factor] using
      stageTransportDistanceBound
        S w h_bound α xCore xStage
  have hfactor_ne : factor ≠ 0 := ne_of_gt hfactorPos
  calc
    ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖
        ≤ ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
            factor * ‖(xStage : H₁) - (xCore : H₁)‖ := htransport
    _ ≤ (1 / 4 : ℝ) ^ n / 4 +
          factor * ((1 / 4 : ℝ) ^ n / (4 * factor)) := by
          exact add_le_add hcore (mul_le_mul_of_nonneg_left hdist hfactorPos.le)
    _ = (1 / 4 : ℝ) ^ n / 4 + (1 / 4 : ℝ) ^ n / 4 := by
          field_simp [factor, hfactor_ne]
    _ = (1 / 4 : ℝ) ^ n / 2 := by
          ring

/-- Helper for Theorem 2.19: a fixed-stage head bound transfers to a later head as soon as the
ambient displacement is already controlled in the transport-budget scale. -/
theorem laterInitialSegmentHeadBoundFromTransportBudget
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (α : ι) (xCore xStage : K.kerᗮ) (n : ℕ)
    (hcore :
      ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 4)
    (hbudget :
      (‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1) *
          ‖(xStage : H₁) - (xCore : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 4) :
    ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖ ≤
      (1 / 4 : ℝ) ^ n / 2 := by
  -- Consume the packaged transport budget directly in the stable fixed-stage transfer estimate.
  calc
    ‖S.reconstructionFamily w h_bound α (K (xStage : H₁)) - (xStage : H₁)‖
        ≤ ‖S.reconstructionFamily w h_bound α (K (xCore : H₁)) - (xCore : H₁)‖ +
            (‖S.reconstructionFamily w h_bound α‖ * ‖K‖ + 1) *
              ‖(xStage : H₁) - (xCore : H₁)‖ := by
          exact stageTransportDistanceBound S w h_bound α xCore xStage
    _ ≤ (1 / 4 : ℝ) ^ n / 4 + (1 / 4 : ℝ) ^ n / 4 := by
          exact add_le_add hcore hbudget
    _ = (1 / 4 : ℝ) ^ n / 2 := by
          ring

/-- Helper for Theorem 2.19: the infinite branch only needs one exact-data block for each
geometric budget, stated directly in the quantities consumed by the block recursion. -/
theorem existsInfiniteLengthExactDataBlock
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (h_length : S.length = ⊤) (n : ℕ) :
    ∃ αBlock : ι, ∃ xBlock : K.kerᗮ,
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xBlock : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 2 ∧
      ‖S.reconstructionFamily w h_bound αBlock (g : H₂) -
          S.reconstructionFamily w h_bound αBlock (K (xBlock : H₁))‖ ≤
        (1 / 4 : ℝ) ^ n / 4 ∧
      ‖S.reconstructionFamily w h_bound αBlock (K (xBlock : H₁)) - (xBlock : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 2 := by
  -- Route correction: the exact-data block is the true owner surface for the infinite branch.
  obtain ⟨δCore, hδCorePos, NCore, happroxCore, hheadCore, hnormCore⟩ :=
    existsInfiniteLengthExactDataRadius
      S w h_bound lα αChoice h_choice h_pointwise h_norm g h_length n
  let αCore : ι := αChoice δCore
  let xCore : K.kerᗮ := S.initialSegmentRangePseudoInverse g h_length NCore
  have happroxCore' :
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xCore : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 8 := by
    -- Freeze one canonical exact-data core stage as the starting point for the direct block route.
    simpa [xCore] using happroxCore
  have hheadCore' :
      ‖S.reconstructionFamily w h_bound αCore (K (xCore : H₁)) - (xCore : H₁)‖ ≤
        (1 / 4 : ℝ) ^ n / 4 := by
    -- The same core stage already carries the desired exact-data head bound on the core head.
    simpa [αCore, xCore] using hheadCore
  have hnormCore' :
      ‖S.reconstructionFamily w h_bound αCore‖ * δCore ≤
        (1 / 4 : ℝ) ^ n / 4 := by
    -- Its norm-product control is also already normalized at the geometric block scale.
    simpa [αCore] using hnormCore
  -- TODO: complete the direct exact-data block route by choosing a same-stage head whose datum
  -- defect is admissible for `αCore`, then combine `hnormCore'` with the fixed-stage transfer
  -- lemmas to obtain the transport and exact-data head bounds required below.
  sorry

/-- Helper for Theorem 2.19: one infinite-branch block should choose a later cutoff, one filter
parameter, and one `K.kerᗮ` head so the approximation, exact-data head error, and noisy-to-head
transport term all fit the geometric stage budget. -/
theorem existsInfiniteLengthChoiceBlock
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂)))
    (h_length : S.length = ⊤)
    (m n : ℕ) :
    ∃ cut : ℕ, ∃ αBlock : ι, ∃ xBlock : K.kerᗮ,
      m < cut ∧
        ‖(K.kerOrthogonalEquivRange.symm g : H₁) - ((xBlock : K.kerᗮ) : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n ∧
        ‖S.reconstructionFamily w h_bound αBlock (K ((xBlock : K.kerᗮ) : H₁)) -
            ((xBlock : K.kerᗮ) : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n ∧
        ∀ k ≥ cut,
          ‖S.reconstructionFamily w h_bound αBlock (gSeq k) -
              S.reconstructionFamily w h_bound αBlock (K ((xBlock : K.kerᗮ) : H₁))‖ ≤
            (1 / 4 : ℝ) ^ n := by
  -- Route correction: the infinite branch now uses one exact-data block plus continuity of the
  -- fixed chosen operator, instead of routing through the dead stage-package family.
  obtain ⟨αBlock, xBlock, happrox, hexactTail, hhead⟩ :=
    existsInfiniteLengthExactDataBlock
      S w h_bound lα αChoice h_choice h_pointwise h_norm g h_length n
  obtain ⟨cut, hcutGt, hcutTail⟩ :=
    existsFixedOperatorTailCutoff
      S w h_bound g gSeq hgSeq αBlock m n
  have hnoiseBlock :
      ∀ k ≥ cut,
        ‖S.reconstructionFamily w h_bound αBlock (gSeq k) -
            S.reconstructionFamily w h_bound αBlock (K (xBlock : H₁))‖ ≤
          (1 / 4 : ℝ) ^ n := by
    intro k hk
    have hsplit :
        S.reconstructionFamily w h_bound αBlock (gSeq k) -
            S.reconstructionFamily w h_bound αBlock (K (xBlock : H₁)) =
          (S.reconstructionFamily w h_bound αBlock (gSeq k) -
              S.reconstructionFamily w h_bound αBlock (g : H₂)) +
            (S.reconstructionFamily w h_bound αBlock (g : H₂) -
              S.reconstructionFamily w h_bound αBlock (K (xBlock : H₁))) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
      abel_nf
    -- The noisy block splits into the fixed-operator noisy tail and the exact-data block error.
    rw [hsplit]
    calc
      ‖(S.reconstructionFamily w h_bound αBlock (gSeq k) -
            S.reconstructionFamily w h_bound αBlock (g : H₂)) +
          (S.reconstructionFamily w h_bound αBlock (g : H₂) -
            S.reconstructionFamily w h_bound αBlock (K (xBlock : H₁)))‖
          ≤ ‖S.reconstructionFamily w h_bound αBlock (gSeq k) -
                S.reconstructionFamily w h_bound αBlock (g : H₂)‖ +
              ‖S.reconstructionFamily w h_bound αBlock (g : H₂) -
                S.reconstructionFamily w h_bound αBlock (K (xBlock : H₁))‖ := by
            exact norm_add_le _ _
      _ ≤ (1 / 4 : ℝ) ^ n / 2 + (1 / 4 : ℝ) ^ n / 4 := by
            exact add_le_add (hcutTail k hk) hexactTail
      _ ≤ (1 / 4 : ℝ) ^ n := by
            have hpow_nonneg : 0 ≤ (1 / 4 : ℝ) ^ n := by
              positivity
            linarith
  refine ⟨cut, αBlock, xBlock, hcutGt, ?_, ?_, ?_⟩
  · -- The exact-data block already carries the required ambient approximation estimate.
    calc
      ‖(K.kerOrthogonalEquivRange.symm g : H₁) - ((xBlock : K.kerᗮ) : H₁)‖
          ≤ (1 / 4 : ℝ) ^ n / 2 := by simpa using happrox
      _ ≤ (1 / 4 : ℝ) ^ n := by
          have hnonneg : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
          linarith
  · -- The direct exact-data block gives a stronger head estimate than the downstream block uses.
    calc
      ‖S.reconstructionFamily w h_bound αBlock (K ((xBlock : K.kerᗮ) : H₁)) -
          ((xBlock : K.kerᗮ) : H₁)‖
          ≤ (1 / 4 : ℝ) ^ n / 2 := by simpa using hhead
      _ ≤ (1 / 4 : ℝ) ^ n := by
          have hnonneg : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
          linarith
  · -- Combine the fixed-operator continuity cutoff with the exact-data block transport term.
    simpa using hnoiseBlock

/-- Helper for Theorem 2.19: recursively iterating one compatible infinite-branch block gives a
strictly increasing cutoff sequence together with blockwise parameters and heads. -/
theorem existsInfiniteLengthChoiceBlocks
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂)))
    (h_length : S.length = ⊤) :
    ∃ cut : ℕ → ℕ, ∃ αBlock : ℕ → ι, ∃ xBlock : ℕ → K.kerᗮ,
      StrictMono cut ∧
        (∀ n,
          ‖(K.kerOrthogonalEquivRange.symm g : H₁) - ((xBlock n : K.kerᗮ) : H₁)‖ ≤
            (1 / 4 : ℝ) ^ n) ∧
        (∀ n,
          ‖S.reconstructionFamily w h_bound (αBlock n) (K ((xBlock n : K.kerᗮ) : H₁)) -
              ((xBlock n : K.kerᗮ) : H₁)‖ ≤
            (1 / 4 : ℝ) ^ n) ∧
        (∀ n, ∀ k ≥ cut n,
          ‖S.reconstructionFamily w h_bound (αBlock n) (gSeq k) -
              S.reconstructionFamily w h_bound (αBlock n) (K ((xBlock n : K.kerᗮ) : H₁))‖ ≤
            (1 / 4 : ℝ) ^ n) := by
  choose cutChoice αChoiceBlock xChoiceBlock hlt happrox hhead hnoise using
    fun m n ↦
      existsInfiniteLengthChoiceBlock
        S w h_bound lα αChoice h_choice h_pointwise h_norm g gSeq hgSeq h_length m n
  let cut : ℕ → ℕ :=
    Nat.rec (cutChoice 0 0) fun n prev ↦ cutChoice prev (n + 1)
  let αBlock : ℕ → ι :=
    Nat.rec (αChoiceBlock 0 0) fun n _prev ↦ αChoiceBlock (cut n) (n + 1)
  let xBlock : ℕ → K.kerᗮ :=
    Nat.rec (xChoiceBlock 0 0) fun n _prev ↦ xChoiceBlock (cut n) (n + 1)
  let xBlockH : ℕ → H₁ := fun n ↦ (xBlock n).1
  have hcutMono : StrictMono cut := by
    -- Each recursive block is chosen strictly after the previous cutoff.
    refine strictMono_nat_of_lt_succ ?_
    intro n
    simpa [cut] using hlt (cut n) (n + 1)
  have happroxBlock :
      ∀ n,
        ‖(K.kerOrthogonalEquivRange.symm g : H₁) - xBlockH n‖ ≤
          (1 / 4 : ℝ) ^ n := by
    intro n
    cases n with
    | zero =>
        -- The zeroth block is the base witness chosen with lower cutoff `0`.
        simpa [xBlockH, xBlock] using happrox 0 0
    | succ n =>
        -- Every later block is chosen from the previous cutoff and the next stage budget.
        simpa [xBlockH, cut, xBlock] using happrox (cut n) (n + 1)
  have hheadBlock :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αBlock n) (K (xBlockH n)) - xBlockH n‖ ≤
          (1 / 4 : ℝ) ^ n := by
    intro n
    cases n with
    | zero =>
        -- The base block inherits its exact-data head bound from the zeroth block witness.
        simpa [xBlockH, αBlock, xBlock] using hhead 0 0
    | succ n =>
        -- The recursive block carries the stagewise exact-data bound chosen at stage `n + 1`.
        simpa [xBlockH, cut, αBlock, xBlock] using hhead (cut n) (n + 1)
  have hnoiseBlock :
      ∀ n, ∀ k ≥ cut n,
        ‖S.reconstructionFamily w h_bound (αBlock n) (gSeq k) -
            S.reconstructionFamily w h_bound (αBlock n) (K (xBlockH n))‖ ≤
          (1 / 4 : ℝ) ^ n := by
    intro n
    cases n with
    | zero =>
        -- The first block keeps its noisy tail bound from the initial witness.
        simpa [xBlockH, cut, αBlock, xBlock] using hnoise 0 0
    | succ n =>
        -- Later blocks inherit their noisy tail estimate from the recursive block witness.
        simpa [xBlockH, cut, αBlock, xBlock] using hnoise (cut n) (n + 1)
  refine ⟨cut, αBlock, xBlock, hcutMono, ?_, ?_, ?_⟩
  · intro n
    -- Fold the ambient-head notation back to the bundled `K.kerᗮ` sequence.
    simpa [xBlockH] using happroxBlock n
  · intro n
    -- Repackage the exact-data head bound through the ambient coercion of `xBlock n`.
    simpa [xBlockH] using hheadBlock n
  · intro n k hk
    -- Repackage the noisy tail bound through the same ambient-head notation.
    simpa [xBlockH] using hnoiseBlock n k hk

/-- Helper for Theorem 2.19: once compatible infinite-branch blocks are available, the cutoff
construction turns them into the parameter sequence required by the `seq` clause. -/
theorem infiniteLengthChoiceSequenceFromBlocks
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (g : K.range) (gSeq : ℕ → H₂)
    (cut : ℕ → ℕ) (hcutMono : StrictMono cut)
    (αBlock : ℕ → ι) (xBlock : ℕ → K.kerᗮ)
    (happrox :
      ∀ n,
        ‖(K.kerOrthogonalEquivRange.symm g : H₁) - ((xBlock n : K.kerᗮ) : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n)
    (hhead :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αBlock n) (K ((xBlock n : K.kerᗮ) : H₁)) -
            ((xBlock n : K.kerᗮ) : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n)
    (hnoise :
      ∀ n, ∀ k ≥ cut n,
        ‖S.reconstructionFamily w h_bound (αBlock n) (gSeq k) -
            S.reconstructionFamily w h_bound (αBlock n) (K ((xBlock n : K.kerᗮ) : H₁))‖ ≤
          (1 / 4 : ℝ) ^ n) :
    ∃ αSeq : ℕ → ι,
      Tendsto
        (fun n ↦
          S.reconstructionFamily w h_bound (αSeq n) (gSeq n))
        atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  let stageOf : ℕ → ℕ := fun k ↦ Nat.findGreatest (fun n ↦ cut n ≤ k) k
  have hcutLower : ∀ n, n ≤ cut n := by
    intro n
    induction n with
    | zero =>
        exact Nat.zero_le (cut 0)
    | succ n ihn =>
        -- A strictly increasing natural cutoff sequence advances by at least one at each step.
        exact le_trans (Nat.succ_le_succ ihn) (Nat.succ_le_of_lt (hcutMono (Nat.lt_succ_self n)))
  have hstageTendsto : Tendsto stageOf atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro n
    refine Filter.mem_atTop_sets.2 ?_
    refine ⟨cut n, fun k hk ↦ ?_⟩
    have hnk : n ≤ k := le_trans (hcutLower n) hk
    -- Once `k` passes `cut n`, the greatest reached cutoff index is at least `n`.
    exact Nat.le_findGreatest (P := fun m ↦ cut m ≤ k) hnk hk
  have hstageCut : ∀ᶠ k : ℕ in atTop, cut (stageOf k) ≤ k := by
    refine Filter.mem_atTop_sets.2 ?_
    refine ⟨cut 0, fun k hk ↦ ?_⟩
    -- Beyond the first cutoff, `stageOf k` is a genuinely attained cutoff level.
    exact Nat.findGreatest_spec (P := fun n ↦ cut n ≤ k) (m := 0) (n := k) (Nat.zero_le _) hk
  let αSeq : ℕ → ι := fun k ↦ αBlock (stageOf k)
  refine ⟨αSeq, ?_⟩
  have hpow :
      Tendsto (fun k ↦ (1 / 4 : ℝ) ^ stageOf k) atTop (𝓝 0) := by
    -- The stage selector still tends to infinity, so the geometric block error vanishes.
    exact
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hstageTendsto
  have hthreePow :
      Tendsto (fun k ↦ (3 : ℝ) * (1 / 4 : ℝ) ^ stageOf k) atTop (𝓝 0) := by
    -- Summing the three blockwise geometric terms still gives a null sequence.
    simpa using tendsto_const_nhds.mul hpow
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Npow, hNpow⟩ := Metric.tendsto_atTop.1 hthreePow ε hε
  rcases Filter.mem_atTop_sets.1 hstageCut with ⟨Ncut, hNcut⟩
  refine ⟨max Npow Ncut, fun k hk ↦ ?_⟩
  have hkpow : Npow ≤ k := le_trans (le_max_left _ _) hk
  have hkcut : Ncut ≤ k := le_trans (le_max_right _ _) hk
  have hcutk : cut (stageOf k) ≤ k := hNcut k hkcut
  let Rk := S.reconstructionFamily w h_bound (αSeq k)
  have hsplit :
      ‖Rk (gSeq k) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
        ‖Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))‖ +
          ‖Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
              ((xBlock (stageOf k) : K.kerᗮ) : H₁)‖ +
            ‖((xBlock (stageOf k) : K.kerᗮ) : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
    -- Compare the noisy reconstruction with the block head chosen for `stageOf k`.
    have hdecomp :
        Rk (gSeq k) - (K.kerOrthogonalEquivRange.symm g : H₁) =
          (Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))) +
            ((Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
                ((xBlock (stageOf k) : K.kerᗮ) : H₁)) +
              (((xBlock (stageOf k) : K.kerᗮ) : H₁) -
                (K.kerOrthogonalEquivRange.symm g : H₁))) := by
      simp [Rk, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hdecomp]
    calc
      ‖(Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))) +
          ((Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
                ((xBlock (stageOf k) : K.kerᗮ) : H₁)) +
            (((xBlock (stageOf k) : K.kerᗮ) : H₁) -
              (K.kerOrthogonalEquivRange.symm g : H₁)))‖
          ≤ ‖Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))‖ +
              ‖(Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
                    ((xBlock (stageOf k) : K.kerᗮ) : H₁)) +
                  (((xBlock (stageOf k) : K.kerᗮ) : H₁) -
                    (K.kerOrthogonalEquivRange.symm g : H₁))‖ := by
            exact norm_add_le _ _
      _ ≤ ‖Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))‖ +
            (‖Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
                ((xBlock (stageOf k) : K.kerᗮ) : H₁)‖ +
              ‖((xBlock (stageOf k) : K.kerᗮ) : H₁) -
                  (K.kerOrthogonalEquivRange.symm g : H₁)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = ‖Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))‖ +
            ‖Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
                ((xBlock (stageOf k) : K.kerᗮ) : H₁)‖ +
              ‖((xBlock (stageOf k) : K.kerᗮ) : H₁) -
                  (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
            ring
  have happrox' :
      ‖((xBlock (stageOf k) : K.kerᗮ) : H₁) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
        (1 / 4 : ℝ) ^ stageOf k := by
    simpa [norm_sub_rev] using happrox (stageOf k)
  have hsumBound :
      ‖Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))‖ +
          ‖Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
              ((xBlock (stageOf k) : K.kerᗮ) : H₁)‖ +
            ‖((xBlock (stageOf k) : K.kerᗮ) : H₁) -
                (K.kerOrthogonalEquivRange.symm g : H₁)‖ ≤
        (1 / 4 : ℝ) ^ stageOf k +
          (1 / 4 : ℝ) ^ stageOf k +
            (1 / 4 : ℝ) ^ stageOf k := by
    -- Bound each of the three block terms by the shared geometric stage budget.
    exact
      add_le_add
        (add_le_add
          (by simpa [αSeq, Rk] using hnoise (stageOf k) k hcutk)
          (by simpa [αSeq, Rk] using hhead (stageOf k)))
        happrox'
  calc
    dist (Rk (gSeq k)) (K.kerOrthogonalEquivRange.symm g : H₁) =
        ‖Rk (gSeq k) - (K.kerOrthogonalEquivRange.symm g : H₁)‖ := by
          rw [dist_eq_norm]
    _ ≤ ‖Rk (gSeq k) - Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁))‖ +
          ‖Rk (K ((xBlock (stageOf k) : K.kerᗮ) : H₁)) -
              ((xBlock (stageOf k) : K.kerᗮ) : H₁)‖ +
            ‖((xBlock (stageOf k) : K.kerᗮ) : H₁) -
                (K.kerOrthogonalEquivRange.symm g : H₁)‖ := hsplit
    _ ≤ (1 / 4 : ℝ) ^ stageOf k +
          (1 / 4 : ℝ) ^ stageOf k +
            (1 / 4 : ℝ) ^ stageOf k := hsumBound
    _ = (3 : ℝ) * (1 / 4 : ℝ) ^ stageOf k := by ring
    _ < ε := by
          have hN' := hNpow k hkpow
          simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg, mul_nonneg] using hN'

/-- Helper for Theorem 2.19: the infinite singular-length branch should directly produce the
parameter sequence required by the `seq` clause, rather than an over-strong synchronized stage
package. -/
theorem existsChoiceSequenceForSeqClause_infinite
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂)))
    (h_length : S.length = ⊤) :
    ∃ αSeq : ℕ → ι,
      Tendsto
        (fun n ↦
          S.reconstructionFamily w h_bound (αSeq n) (gSeq n))
        atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  -- Route correction: the infinite branch still consumes recursive blocks here, but the actual
  -- same-stage obstruction has been reduced to the direct owner theorem
  -- `existsInfiniteLengthExactDataBlock`.
  obtain ⟨cut, αBlock, xBlock, hcutMono, happrox, hhead, hnoise⟩ :=
    existsInfiniteLengthChoiceBlocks
      S w h_bound lα αChoice h_choice h_pointwise h_norm g gSeq hgSeq h_length
  -- Package the recursive blocks into the `seq`-clause parameter choice on the original data.
  exact
    infiniteLengthChoiceSequenceFromBlocks
      S w h_bound g gSeq cut hcutMono αBlock xBlock happrox hhead hnoise

/-- Helper for Theorem 2.19: the exact-data part of the infinite branch only needs the five
stagewise bounds from the synchronized stage package. -/
theorem exactDataConvergesFromStagePackage
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (g : K.range) (δStage : ℕ → ℝ) (xStage : ℕ → K.kerᗮ)
    (happrox :
      ∀ n, ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xStage n : H₁)‖ ≤ (1 / 4 : ℝ) ^ n)
    (hdata :
      ∀ n, ‖(g : H₂) - K (xStage n : H₁)‖ ≤ δStage n)
    (hhead :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δStage n))
              (K (xStage n : H₁)) -
            (xStage n : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n)
    (hnorm :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δStage n))‖ * δStage n ≤
          (1 / 4 : ℝ) ^ n) :
    Tendsto
      (fun n ↦
        S.reconstructionFamily w h_bound (αChoice (δStage n)) (g : H₂))
      atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  have htail :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δStage n)) (g : H₂) -
            S.reconstructionFamily w h_bound (αChoice (δStage n))
              (K (xStage n : H₁))‖ ≤
          (1 / 4 : ℝ) ^ n := by
    intro n
    -- The datum-tail part is the operator-norm estimate plus the stage-package radius bound.
    calc
      ‖S.reconstructionFamily w h_bound (αChoice (δStage n)) (g : H₂) -
          S.reconstructionFamily w h_bound (αChoice (δStage n))
            (K (xStage n : H₁))‖
          ≤ ‖S.reconstructionFamily w h_bound (αChoice (δStage n))‖ *
              ‖(g : H₂) - K (xStage n : H₁)‖ := by
            simpa using
              reconstructionFamily_apply_sub_le
                S w h_bound (αChoice (δStage n)) (g : H₂) (K (xStage n : H₁))
      _ ≤ ‖S.reconstructionFamily w h_bound (αChoice (δStage n))‖ * δStage n := by
            exact mul_le_mul_of_nonneg_left (hdata n) (norm_nonneg _)
      _ ≤ (1 / 4 : ℝ) ^ n := hnorm n
  -- Feed the synchronized stage package into the existing exact-data convergence consumer.
  simpa using
    exactDataConvergesFromNormalizedSchedule
      S w h_bound (fun n ↦ αChoice (δStage n)) g xStage happrox htail hhead

/-- Helper for Theorem 2.19: a strictly increasing cutoff can be turned into a stage selector
that tends to infinity and is eventually admissible for the cutoff tail bounds. -/
theorem existsStageIndexFromCutoff
    (cut : ℕ → ℕ) (hcutMono : StrictMono cut) :
    ∃ stageOf : ℕ → ℕ,
      Tendsto stageOf atTop atTop ∧
      ∀ᶠ k in atTop, cut (stageOf k) ≤ k := by
  let stageOf : ℕ → ℕ := fun k ↦ Nat.findGreatest (fun n ↦ cut n ≤ k) k
  have hcutLower : ∀ n, n ≤ cut n := by
    intro n
    induction n with
    | zero =>
        exact Nat.zero_le (cut 0)
    | succ n ihn =>
        -- A strictly increasing natural sequence advances by at least one at every step.
        exact le_trans (Nat.succ_le_succ ihn) (Nat.succ_le_of_lt (hcutMono (Nat.lt_succ_self n)))
  have hstageTendsto : Tendsto stageOf atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro n
    refine Filter.mem_atTop_sets.2 ?_
    refine ⟨cut n, fun k hk ↦ ?_⟩
    have hnk : n ≤ k := le_trans (hcutLower n) hk
    -- Once `k` passes `cut n`, the greatest reached cutoff index is at least `n`.
    exact Nat.le_findGreatest (P := fun m ↦ cut m ≤ k) hnk hk
  have hstageCut : ∀ᶠ k : ℕ in atTop, cut (stageOf k) ≤ k := by
    refine Filter.mem_atTop_sets.2 ?_
    refine ⟨cut 0, fun k hk ↦ ?_⟩
    -- Beyond the first cutoff, the chosen stage index really is an attained cutoff level.
    exact Nat.findGreatest_spec (P := fun n ↦ cut n ≤ k) (m := 0) (n := k) (Nat.zero_le _) hk
  exact ⟨stageOf, hstageTendsto, hstageCut⟩

/-- Helper for Theorem 2.19: once the infinite-branch stage package is available, the
cutoff construction lifts it from exact data to the original noisy sequence. -/
theorem infiniteLengthChoiceSequenceFromStagePackage
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (αChoice : ℝ → ι)
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂)))
    (δStage : ℕ → ℝ) (xStage : ℕ → K.kerᗮ)
    (hδStagePos : ∀ n, 0 < δStage n)
    (happrox :
      ∀ n, ‖(K.kerOrthogonalEquivRange.symm g : H₁) - (xStage n : H₁)‖ ≤ (1 / 4 : ℝ) ^ n)
    (hdata :
      ∀ n, ‖(g : H₂) - K (xStage n : H₁)‖ ≤ δStage n)
    (hhead :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δStage n))
              (K (xStage n : H₁)) -
            (xStage n : H₁)‖ ≤
          (1 / 4 : ℝ) ^ n)
    (hnorm :
      ∀ n,
        ‖S.reconstructionFamily w h_bound (αChoice (δStage n))‖ * δStage n ≤
          (1 / 4 : ℝ) ^ n) :
    ∃ αSeq : ℕ → ι,
      Tendsto
        (fun n ↦
          S.reconstructionFamily w h_bound (αSeq n) (gSeq n))
        atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  obtain ⟨cut, hcutMono, hcutTail⟩ :=
    existsIncreasingTailCutoff gSeq hgSeq δStage hδStagePos
  obtain ⟨stageOf, hstageTendsto, hstageCut⟩ :=
    existsStageIndexFromCutoff cut hcutMono
  let αSeq : ℕ → ι := fun k ↦ αChoice (δStage (stageOf k))
  refine ⟨αSeq, ?_⟩
  have hexactStage :
      Tendsto
        (fun n ↦
          S.reconstructionFamily w h_bound (αChoice (δStage n)) (g : H₂))
        atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
    -- The synchronized stage package already gives convergence on exact data.
    exact
      exactDataConvergesFromStagePackage
        S w h_bound αChoice g δStage xStage happrox hdata hhead hnorm
  have hexact :
      Tendsto
        (fun k ↦ S.reconstructionFamily w h_bound (αSeq k) (g : H₂))
        atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
    -- Compose the exact-data convergence with the stage selector built from the cutoff.
    change
      Tendsto
        ((fun n ↦ S.reconstructionFamily w h_bound (αChoice (δStage n)) (g : H₂)) ∘ stageOf)
        atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁))
    exact hexactStage.comp hstageTendsto
  have hpow :
      Tendsto (fun k ↦ (1 / 4 : ℝ) ^ stageOf k) atTop (𝓝 (0 : ℝ)) := by
    -- The blockwise selector still tends to infinity, so the geometric tail remains vanishing.
    exact
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hstageTendsto
  have hnoiseNorm :
      Tendsto
        (fun k ↦
          ‖S.reconstructionFamily w h_bound (αSeq k) (gSeq k) -
              S.reconstructionFamily w h_bound (αSeq k) (g : H₂)‖)
        atTop (𝓝 0) := by
    have hbound :
        ∀ᶠ k : ℕ in atTop,
          ‖S.reconstructionFamily w h_bound (αSeq k) (gSeq k) -
              S.reconstructionFamily w h_bound (αSeq k) (g : H₂)‖ ≤
            (1 / 4 : ℝ) ^ stageOf k := by
      filter_upwards [hstageCut] with k hk
      -- Once `k` has passed the chosen cutoff, the noisy datum lies inside the matching stage ball.
      calc
        ‖S.reconstructionFamily w h_bound (αSeq k) (gSeq k) -
            S.reconstructionFamily w h_bound (αSeq k) (g : H₂)‖
            ≤ ‖S.reconstructionFamily w h_bound (αSeq k)‖ * ‖gSeq k - (g : H₂)‖ := by
              simpa [αSeq] using
                reconstructionFamily_apply_sub_le
                  S w h_bound (αSeq k) (gSeq k) (g : H₂)
        _ ≤ ‖S.reconstructionFamily w h_bound (αSeq k)‖ * δStage (stageOf k) := by
              exact mul_le_mul_of_nonneg_left (hcutTail (stageOf k) k hk) (norm_nonneg _)
        _ ≤ (1 / 4 : ℝ) ^ stageOf k := by
              simpa [αSeq] using hnorm (stageOf k)
    -- Squeeze the noisy perturbation by the geometric envelope selected through `stageOf`.
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds
        hpow
        (Filter.Eventually.of_forall fun k ↦ norm_nonneg _)
        hbound
  have hnoise :
      Tendsto
        (fun k ↦
          S.reconstructionFamily w h_bound (αSeq k) (gSeq k) -
            S.reconstructionFamily w h_bound (αSeq k) (g : H₂))
        atTop (𝓝 (0 : H₁)) := by
    -- Convert the norm convergence of the noisy part back to vector convergence.
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnoiseNorm
  -- Add the vanishing noisy perturbation to the exact-data convergence.
  simpa [αSeq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hnoise.add hexact

/-- Helper for Theorem 2.19: every convergent noisy data sequence admits a parameter choice
realizing the `seq` clause from Definition 2.18. -/
theorem existsChoiceSequenceForSeqClause
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (g : K.range) (gSeq : ℕ → H₂)
    (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂))) :
    ∃ αSeq : ℕ → ι,
      Tendsto
        (fun n ↦
          S.reconstructionFamily w h_bound (αSeq n) (gSeq n))
        atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  by_cases h_length : S.length = ⊤
  · -- Route correction: the `seq` clause is the correct owner surface, but the infinite-length
    -- branch should be handled by a dedicated exact-data diagonal theorem.
    exact
      existsChoiceSequenceForSeqClause_infinite
        S w h_bound lα αChoice h_choice h_pointwise h_norm g gSeq hgSeq h_length
  · let δBuf : ℕ → ℝ := fun n ↦ ‖gSeq n - (g : H₂)‖ + (1 / 4 : ℝ) ^ n
    let αSeq : ℕ → ι := fun n ↦ αChoice (δBuf n)
    refine ⟨αSeq, ?_⟩
    have hexact :
        Tendsto
          (fun n ↦ S.reconstructionFamily w h_bound (αSeq n) (g : H₂))
          atTop (𝓝 (K.kerOrthogonalEquivRange.symm g : H₁)) := by
      -- In finite singular length, the raw buffered choice already gives exact-data convergence.
      simpa [αSeq, δBuf] using
        finiteLengthExactDataConvergesAlongBufferedChoice
          S w h_bound lα αChoice h_choice h_pointwise g gSeq hgSeq h_length
    have hnoise :
        Tendsto
          (fun n ↦
            S.reconstructionFamily w h_bound (αSeq n) (gSeq n) -
              S.reconstructionFamily w h_bound (αSeq n) (g : H₂))
          atTop (𝓝 (0 : H₁)) := by
      -- The same buffered choice also drives the purely noisy perturbation to `0`.
      exact
        tendsto_zero_iff_norm_tendsto_zero.2 <|
          by simpa [αSeq, δBuf] using
            bufferedChoiceNoiseBound_tendstoZero
              S w h_bound αChoice h_norm g gSeq hgSeq
    -- Combine the exact-data convergence with the vanishing noisy perturbation.
    simpa [αSeq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hnoise.add hexact

/-- thm_2_19. Theorem 2.19 (2). Main labeled source-facing entry.

Assume `sup_s |w α (s ^ 2) / s| < ∞` for each `α`, that
`w α (s ^ 2) → 1` for each `s > 0` along the limiting parameter filter `lα`,
that `αChoice δ` tends to `lα` as `δ → 0+`, and that
`‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ → 0` as `δ → 0+`. Then the reconstruction
family from `(2.24)` converges to `K†` on `K.range`, realized here by the canonical
range inverse `fun g ↦ (K.kerOrthogonalEquivRange.symm g : H₁)` on exact data in `K.range`. -/
theorem reconstructionOperator_convergesToCanonicalInverseOnRange
    (S : SingularSystem K) (w : ι → ℝ → ℝ)
    (h_bound : ∀ α, ∃ C ≥ 0, ∀ s > 0, |w α (s ^ 2) / s| ≤ C)
    (lα : Filter ι)
    (αChoice : ℝ → ι)
    (h_choice :
      Tendsto αChoice (nhdsWithin 0 (Set.Ioi 0)) lα)
    (h_pointwise :
      ∀ s : ℝ, 0 < s →
        Tendsto (fun α : ι ↦ w α (s ^ 2)) lα (𝓝 1))
    (h_norm :
      Tendsto
        (fun δ ↦ ‖S.reconstructionFamily w h_bound (αChoice δ)‖ * δ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    FilterRegularization.ConvergesTo K
      (fun α g ↦ S.reconstructionFamily w h_bound α g)
      (fun g ↦ (K.kerOrthogonalEquivRange.symm g : H₁)) := by
  -- Build the regularization scheme from continuity of each operator and the sequence criterion.
  refine
    FilterRegularization.ConvergesTo.ofContinuousAndSeq
      K
      (fun α g ↦ S.reconstructionFamily w h_bound α g)
      (fun g ↦ (K.kerOrthogonalEquivRange.symm g : H₁))
      ?_
      ?_
  · intro α
    -- Continuity follows from the already established linearity of the reconstruction family.
    exact
      FilterRegularization.IsLinear.continuous
        (reconstructionOperator_isLinear S w h_bound)
        α
  · intro g gSeq hgSeq
    -- Route correction: the `seq` clause is existential, so the correct owner surface is now the
    -- dedicated parameter-choice theorem rather than a raw buffered exact-data theorem.
    exact
      existsChoiceSequenceForSeqClause
        S w h_bound lα αChoice h_choice h_pointwise h_norm g gSeq hgSeq

end ContinuousLinearMap.SingularSystem
