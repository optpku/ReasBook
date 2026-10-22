/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_5_1.Iteration
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_13.NegLogLikelihood
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_14.Likelihood
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_10
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_38
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

open scoped BigOperators Topology

namespace PoissonInverse

/-- Membership in `PoissonInverse.logLikelihoodConstraintSet` is exactly the
nonnegativity, positive forward-data, and mass-conservation package from
Exercise 9.14. -/
theorem mem_logLikelihoodConstraintSet
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n)) :
    f ∈ logLikelihoodConstraintSet K d ↔
      f ∈ NonnegativeOrthant.feasibleSet n ∧
        (∀ i : Fin m, 0 < Matrix.mulVec K f i) ∧
          ∑ i : Fin m, Matrix.mulVec K f i = ∑ i : Fin m, d i := by
  -- Expand the constraint set through admissibility to expose the source-facing package.
  rw [PoissonInverse.mem_logLikelihoodConstraintSet_iff, PoissonInverse.mem_admissibleSet_iff]
  constructor
  · rintro ⟨hfeasible, hmass⟩
    exact ⟨hfeasible.1, hfeasible.2, hmass⟩
  · rintro ⟨hfeasible, hforward, hmass⟩
    exact ⟨⟨hfeasible, hforward⟩, hmass⟩

/-- Helper for Exercise 9.14: positive forward data make
`PoissonInverse.negLogLikelihood K d` Fréchet differentiable with the expected
finite-sum linearization. -/
-- TODO: Differentiate each coordinate term `x ↦ [K x]ᵢ - dᵢ log [K x]ᵢ`
-- through the linear forward map, then sum the resulting linear maps.
theorem hasFDerivAt_negLogLikelihood
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n))
    (hforward : ∀ i : Fin m, 0 < Matrix.mulVec K f i) :
    HasFDerivAt
      (negLogLikelihood K d)
      (∑ i : Fin m,
        (1 - d i / Matrix.mulVec K f i) •
          ((EuclideanSpace.proj i).comp (Matrix.toEuclideanLin K).toContinuousLinearMap))
      f := by
  let coordCLM : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun i ↦ (EuclideanSpace.proj i).comp (Matrix.toEuclideanLin K).toContinuousLinearMap
  let arg : Fin m → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x ↦ coordCLM i x
  let coeff : Fin m → ℝ :=
    fun i ↦ 1 - d i / Matrix.mulVec K f i
  have harg :
      ∀ i : Fin m, HasFDerivAt (arg i) (coordCLM i) f := by
    intro i
    simpa [arg] using (coordCLM i).hasFDerivAt
  have hterm :
      ∀ i : Fin m,
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ arg i x - d i * Real.log (arg i x))
          (coeff i • coordCLM i)
          f := by
    intro i
    have hlog :
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ Real.log (arg i x))
          ((arg i f)⁻¹ • coordCLM i)
          f := by
      have hargf : arg i f = Matrix.mulVec K f i := by
        simp [arg, coordCLM, EuclideanSpace.proj]
      exact (harg i).log (by simpa [hargf] using (hforward i).ne')
    have hscaled :
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ d i * Real.log (arg i x))
          (d i • ((arg i f)⁻¹ • coordCLM i))
          f := by
      simpa using hlog.const_mul (d i)
    have hsub :
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ arg i x - d i * Real.log (arg i x))
          (coordCLM i - d i • ((arg i f)⁻¹ • coordCLM i))
          f :=
      (harg i).sub hscaled
    have hderiv :
        coordCLM i - d i • ((arg i f)⁻¹ • coordCLM i) = coeff i • coordCLM i := by
      ext x
      have hargf : arg i f = Matrix.mulVec K f i := by
        simp [arg, coordCLM, EuclideanSpace.proj]
      rw [hargf]
      simp [coeff, smul_eq_mul, sub_eq_add_neg]
      ring
    simpa [hderiv] using hsub
  have hsum :
      HasFDerivAt
        (fun x : EuclideanSpace ℝ (Fin n) ↦
          ∑ i : Fin m, (arg i x - d i * Real.log (arg i x)))
        (∑ i : Fin m, coeff i • coordCLM i)
        f := by
    exact HasFDerivAt.fun_sum fun i _ ↦ hterm i
  refine hsum.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [negLogLikelihood_def]
    simp [arg, coordCLM, EuclideanSpace.proj, Finset.sum_sub_distrib]

/-- Helper for Exercise 9.14: the gradient of `PoissonInverse.negLogLikelihood`
has the source-facing coordinate formula from `(9.56)`. -/
-- TODO: Apply `gradient_apply_eq_fderiv_single` to
-- `hasFDerivAt_negLogLikelihood`, then evaluate the resulting linear map on the
-- standard basis vector.
theorem gradient_negLogLikelihood_apply
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n))
    (hforward : ∀ i : Fin m, 0 < Matrix.mulVec K f i)
    (j : Fin n) :
    gradient (negLogLikelihood K d) f j =
      RichardsonLucy.columnSum K j -
        ∑ i : Fin m, K i j * (d i / Matrix.mulVec K f i) := by
  -- Evaluate the Fréchet derivative on the `j`-th basis vector and simplify.
  rw [gradient_apply_eq_fderiv_single]
  have hderiv := (hasFDerivAt_negLogLikelihood K d f hforward).fderiv
  rw [hderiv]
  have happly :
      (∑ i : Fin m,
          (1 - d i / Matrix.mulVec K f i) •
            ((EuclideanSpace.proj i).comp (Matrix.toEuclideanLin K).toContinuousLinearMap))
        (EuclideanSpace.single j (1 : ℝ))
        =
      ∑ i : Fin m,
        (1 - d i / Matrix.mulVec K f i) *
          Matrix.toEuclideanLin K (EuclideanSpace.single j (1 : ℝ)) i := by
    simp [sum_apply, smul_apply, EuclideanSpace.proj]
  rw [happly]
  calc
    ∑ i : Fin m,
        (1 - d i / Matrix.mulVec K f i) *
          Matrix.toEuclideanLin K (EuclideanSpace.single j (1 : ℝ)) i
        =
      ∑ i : Fin m, (1 - d i / Matrix.mulVec K f i) * K i j := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hsingle :
              Matrix.toEuclideanLin K (EuclideanSpace.single j (1 : ℝ)) i = K i j := by
            simpa using
              congrArg (fun v : Fin m → ℝ ↦ v i)
                (Matrix.ofLp_toEuclideanLin_apply K (EuclideanSpace.single j (1 : ℝ)))
          rw [hsingle]
    _ =
      ∑ i : Fin m, K i j - ∑ i : Fin m, K i j * (d i / Matrix.mulVec K f i) := by
          calc
            ∑ i : Fin m, (1 - d i / Matrix.mulVec K f i) * K i j
                = ∑ i : Fin m, (K i j - K i j * (d i / Matrix.mulVec K f i)) := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    ring
            _ = ∑ i : Fin m, K i j - ∑ i : Fin m, K i j * (d i / Matrix.mulVec K f i) := by
                    rw [Finset.sum_sub_distrib]
    _ =
      RichardsonLucy.columnSum K j -
        ∑ i : Fin m, K i j * (d i / Matrix.mulVec K f i) := by
          have hcol :
              RichardsonLucy.columnSum K j = ∑ i : Fin m, K i j := by
            simpa [Matrix.mulVec, dotProduct] using
              congrArg (fun g : Fin n → ℝ ↦ g j)
                (RichardsonLucy.columnSum_eq_mulVec_transpose_one K)
          rw [hcol]

/-- Helper for Exercise 9.14: on the mass-constrained likelihood set, the
weighted gradient sum of `PoissonInverse.negLogLikelihood K d` vanishes. -/
-- TODO: Insert the coordinate formula from
-- `gradient_negLogLikelihood_apply`, swap the finite sums, and use the mass
-- identity from `hf_mem`.
theorem sum_mul_gradient_negLogLikelihood_eq_zero
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n))
    (hf_mem : f ∈ logLikelihoodConstraintSet K d) :
    ∑ j : Fin n, f j * gradient (negLogLikelihood K d) f j = 0 := by
  obtain ⟨_, hforward, hmass⟩ := (mem_logLikelihoodConstraintSet K d f).mp hf_mem
  let ratio : Fin m → ℝ := fun i ↦ d i / Matrix.mulVec K f i
  have hcol (j : Fin n) :
      RichardsonLucy.columnSum K j = ∑ i : Fin m, K i j := by
    simpa [Matrix.mulVec, dotProduct] using
      congrArg (fun g : Fin n → ℝ ↦ g j)
        (RichardsonLucy.columnSum_eq_mulVec_transpose_one K)
  have hsumColumn :
      ∑ j : Fin n, f j * RichardsonLucy.columnSum K j =
        ∑ i : Fin m, Matrix.mulVec K f i := by
    calc
      ∑ j : Fin n, f j * RichardsonLucy.columnSum K j
          = ∑ j : Fin n, f j * ∑ i : Fin m, K i j := by
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [hcol]
      _ = ∑ j : Fin n, ∑ i : Fin m, f j * K i j := by
            simp_rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ j : Fin n, f j * K i j := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin m, Matrix.mulVec K f i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            simp [Matrix.mulVec, dotProduct, mul_comm]
  have hsumRatio :
      ∑ j : Fin n, f j * ∑ i : Fin m, K i j * ratio i = ∑ i : Fin m, d i := by
    calc
      ∑ j : Fin n, f j * ∑ i : Fin m, K i j * ratio i
          = ∑ j : Fin n, ∑ i : Fin m, f j * (K i j * ratio i) := by
              simp_rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ j : Fin n, f j * (K i j * ratio i) := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin m, ratio i * ∑ j : Fin n, K i j * f j := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Finset.mul_sum (s := Finset.univ) (a := ratio i) (f := fun j ↦ K i j * f j)).symm
      _ = ∑ i : Fin m, ratio i * Matrix.mulVec K f i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            simp [Matrix.mulVec, dotProduct]
      _ = ∑ i : Fin m, d i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have hne : Matrix.mulVec K f i ≠ 0 := (hforward i).ne'
            simp [ratio, div_eq_mul_inv, hne]
  calc
    ∑ j : Fin n, f j * gradient (negLogLikelihood K d) f j
        = ∑ j : Fin n,
            (f j * RichardsonLucy.columnSum K j -
              f j * ∑ i : Fin m, K i j * ratio i) := by
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [gradient_negLogLikelihood_apply K d f hforward j]
              simp [ratio]
              ring
    _ = (∑ j : Fin n, f j * RichardsonLucy.columnSum K j) -
          ∑ j : Fin n, f j * ∑ i : Fin m, K i j * ratio i := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ i : Fin m, Matrix.mulVec K f i - ∑ i : Fin m, d i := by
            rw [hsumColumn, hsumRatio]
    _ = 0 := by
            rw [hmass, sub_self]

/-- Helper for Exercise 9.14: `PoissonInverse.logLikelihoodConstraintSet K d`
is convex because it intersects the nonnegative orthant with strict linear
forward-data inequalities and one affine mass constraint. -/
theorem convex_logLikelihoodConstraintSet
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) :
    Convex ℝ (logLikelihoodConstraintSet K d) := by
  intro x hx y hy a b ha hb hab
  rw [mem_logLikelihoodConstraintSet K d] at hx hy ⊢
  rcases hx with ⟨hx_feasible, hx_forward, hx_mass⟩
  rcases hy with ⟨hy_feasible, hy_forward, hy_mass⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [NonnegativeOrthant.mem_feasibleSet] at hx_feasible hy_feasible ⊢
    intro k
    have hxk := hx_feasible k
    have hyk := hy_feasible k
    change 0 ≤ a * x k + b * y k
    nlinarith
  · intro i
    have hx_pos : 0 < Matrix.mulVec K x i := hx_forward i
    have hy_pos : 0 < Matrix.mulVec K y i := hy_forward i
    calc
      0 < a * Matrix.mulVec K x i + b * Matrix.mulVec K y i := by
            by_cases ha0 : a = 0
            · have hb1 : b = 1 := by nlinarith [hab, ha0]
              simpa [ha0, hb1] using hy_pos
            · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
              by_cases hb0 : b = 0
              · have ha1 : a = 1 := by nlinarith [hab, hb0]
                simpa [hb0, ha1] using hx_pos
              · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
                exact add_pos (mul_pos hapos hx_pos) (mul_pos hbpos hy_pos)
      _ = Matrix.mulVec K (a • x + b • y) i := by
            simp [Matrix.mulVec_add, Matrix.mulVec_smul]
  · calc
      ∑ i : Fin m, Matrix.mulVec K (a • x + b • y) i
          = a * ∑ i : Fin m, Matrix.mulVec K x i + b * ∑ i : Fin m, Matrix.mulVec K y i := by
              simp [Matrix.mulVec_add, Matrix.mulVec_smul, Finset.sum_add_distrib, Finset.mul_sum]
      _ = a * ∑ i : Fin m, d i + b * ∑ i : Fin m, d i := by
            rw [hx_mass, hy_mass]
      _ = ∑ i : Fin m, d i := by
            rw [← add_mul, hab, one_mul]

/-- Helper for Exercise 9.14: rescaling the single-coordinate perturbation
`f + t eⱼ` by the mass-correcting factor
`(∑ i, d i) / (∑ i, d i + t * RichardsonLucy.columnSum K j)` preserves the
Exercise 9.14 constraint set whenever the denominator and perturbed forward
data stay positive. -/
theorem scaledSinglePerturb_mem_logLikelihoodConstraintSet
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n))
    (hf_mem : f ∈ logLikelihoodConstraintSet K d)
    (j : Fin n)
    (t : ℝ)
    (hs_pos : 0 < ∑ i : Fin m, d i)
    (hden : 0 < ∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)
    (hcoord : 0 ≤ f j + t)
    (hforward_t : ∀ i : Fin m, 0 < Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ)) i) :
    ((∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)) •
      (f + t • EuclideanSpace.single j (1 : ℝ)) ∈ logLikelihoodConstraintSet K d := by
  obtain ⟨hf_feasible, _, hf_mass⟩ := (mem_logLikelihoodConstraintSet K d f).mp hf_mem
  have hscale_pos :
      0 <
        (∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j) :=
    div_pos hs_pos hden
  have hscale_nonneg :
      0 ≤
        (∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j) :=
    hscale_pos.le
  have hcol (j : Fin n) :
      RichardsonLucy.columnSum K j = ∑ i : Fin m, K i j := by
    simpa [Matrix.mulVec, dotProduct] using
      congrArg (fun g : Fin n → ℝ ↦ g j)
        (RichardsonLucy.columnSum_eq_mulVec_transpose_one K)
  rw [mem_logLikelihoodConstraintSet K d]
  refine ⟨?_, ?_, ?_⟩
  · rw [NonnegativeOrthant.mem_feasibleSet] at hf_feasible ⊢
    intro k
    by_cases hk : k = j
    · subst hk
      simpa [EuclideanSpace.single, mul_add] using
        (mul_nonneg hscale_nonneg hcoord)
    · simpa [EuclideanSpace.single, hk, hscale_nonneg] using
        mul_nonneg hscale_nonneg (hf_feasible k)
  · intro i
    have hvec :
        (((∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)) •
          (f + t • EuclideanSpace.single j (1 : ℝ))).ofLp
          =
        ((∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)) •
          (f.ofLp + t • (EuclideanSpace.single j (1 : ℝ)).ofLp) := by
      simp [WithLp.ofLp_smul, WithLp.ofLp_add]
    rw [hvec, Matrix.mulVec_smul]
    simpa using mul_pos hscale_pos (hforward_t i)
  · calc
      ∑ i : Fin m,
          Matrix.mulVec K
            (((∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)) •
              (f + t • EuclideanSpace.single j (1 : ℝ))) i
          =
        ((∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)) *
          ∑ i : Fin m, Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ)) i := by
            let scale : ℝ :=
              (∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)
            calc
              ∑ i : Fin m, Matrix.mulVec K (scale • (f + t • EuclideanSpace.single j (1 : ℝ))) i
                  = ∑ i : Fin m, (scale • Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ))) i := by
                      rw [Matrix.mulVec_smul]
              _ = scale * ∑ i : Fin m, Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ)) i := by
                    simp [Finset.mul_sum, Pi.smul_apply]
              _ = ((∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)) *
                    ∑ i : Fin m, Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ)) i := by
                      simp [scale]
      _ =
        ((∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)) *
          (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j) := by
            congr 1
            calc
              ∑ i : Fin m, Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ)) i
                  = ∑ i : Fin m, Matrix.mulVec K f i +
                      ∑ i : Fin m, Matrix.mulVec K (t • EuclideanSpace.single j (1 : ℝ)) i := by
                        simp [Matrix.mulVec_add, Pi.add_apply, Finset.sum_add_distrib]
              _ = ∑ i : Fin m, Matrix.mulVec K f i + t * ∑ i : Fin m, K i j := by
                    congr 1
                    calc
                      ∑ i : Fin m, Matrix.mulVec K (t • EuclideanSpace.single j (1 : ℝ)) i
                          = ∑ i : Fin m, t * K i j := by
                              refine Finset.sum_congr rfl fun i _ ↦ ?_
                              have hsingle :
                                  K.mulVec (EuclideanSpace.single j (1 : ℝ)).ofLp i = K i j := by
                                simpa [Matrix.col_apply] using
                                  congrArg (fun v : Fin m → ℝ ↦ v i) (Matrix.mulVec_single_one K j)
                              rw [Matrix.mulVec_smul]
                              simp [Pi.smul_apply, hsingle, mul_comm]
                      _ = t * ∑ i : Fin m, K i j := by
                            rw [Finset.mul_sum]
              _ = ∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j := by
                    rw [hf_mass, ← hcol j]
      _ = ∑ i : Fin m, d i := by
            field_simp [hden.ne']

/-- exercise_9_14. If `f ∈ logLikelihoodConstraintSet K d` and `f`
maximizes the Poisson log-likelihood `(9.41)` on the Chapter 9 constraint set
given by nonnegativity, positive forward data, and the mass identity `(9.43)`,
then `f` is a critical point for `J(f) = -ℓ(f; d)` from `(9.44)`. -/
-- TODO: Rewrite `negLogLikelihood` to `mass - logLikelihood` on the
-- constraint set, use the local minimum of this rewritten objective, and test
-- the derivative against the mass-preserving direction
-- `eⱼ - (RichardsonLucy.columnSum K j / ∑ i, d i) • f`.
theorem isCriticalPoint_negLogLikelihood_of_isMaxOn_logLikelihood
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n))
    (hf_mem : f ∈ logLikelihoodConstraintSet K d)
    (hmax : IsMaxOn (logLikelihood K d) (logLikelihoodConstraintSet K d) f) :
    NonnegativeOrthant.IsCriticalPoint (negLogLikelihood K d) f := by
  obtain ⟨hf_feasible, hforward, hmass⟩ := (mem_logLikelihoodConstraintSet K d f).mp hf_mem
  have hf_nonneg : ∀ j : Fin n, 0 ≤ f j := by
    simpa [NonnegativeOrthant.mem_feasibleSet] using hf_feasible
  have hmin :
      IsLocalMinOn (negLogLikelihood K d) (logLikelihoodConstraintSet K d) f := by
    refine (show IsMinOn (negLogLikelihood K d) (logLikelihoodConstraintSet K d) f from ?_).localize
    rw [isMinOn_iff]
    intro x hx
    have hlog :
        ∑ i : Fin m, d i * Real.log (Matrix.mulVec K x i) ≤
          ∑ i : Fin m, d i * Real.log (Matrix.mulVec K f i) := by
      simpa [logLikelihood_def] using (isMaxOn_iff.mp hmax) x hx
    have hxmass := sum_mulVec_eq_sum_data_of_mem_logLikelihoodConstraintSet hx
    have hineq :
        ∑ i : Fin m, Matrix.mulVec K f i -
            ∑ i : Fin m, d i * Real.log (Matrix.mulVec K f i) ≤
          ∑ i : Fin m, Matrix.mulVec K x i -
            ∑ i : Fin m, d i * Real.log (Matrix.mulVec K x i) := by
      nlinarith [hlog, hmass, hxmass]
    simpa [negLogLikelihood_def, Finset.sum_sub_distrib] using hineq
  have hJ_diff : DifferentiableAt ℝ (negLogLikelihood K d) f :=
    (hasFDerivAt_negLogLikelihood K d f hforward).differentiableAt
  have hsum_zero := sum_mul_gradient_negLogLikelihood_eq_zero K d f hf_mem
  have hgrad_nonneg : ∀ j : Fin n, 0 ≤ gradient (negLogLikelihood K d) f j := by
    intro j
    by_cases hm : m = 0
    · have hgrad_zero : gradient (negLogLikelihood K d) f j = 0 := by
        have hcol_zero : RichardsonLucy.columnSum K j = 0 := by
          subst hm
          simpa [Matrix.mulVec, dotProduct] using
            congrArg (fun g : Fin n → ℝ ↦ g j)
              (RichardsonLucy.columnSum_eq_mulVec_transpose_one K)
        have hsum_zero :
            ∑ i : Fin m, K i j * (d i / Matrix.mulVec K f i) = 0 := by
          subst hm
          simp
        rw [gradient_negLogLikelihood_apply K d f hforward j, hcol_zero, hsum_zero]
        simp
      simp [hgrad_zero]
    · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      let i0 : Fin m := ⟨0, hm_pos⟩
      have hs_pos_forward : 0 < ∑ i : Fin m, Matrix.mulVec K f i := by
        have hle :
            Matrix.mulVec K f i0 ≤ ∑ i : Fin m, Matrix.mulVec K f i := by
          simpa using
            (Finset.single_le_sum
              (fun i _ ↦ (hforward i).le)
              (by simp : i0 ∈ (Finset.univ : Finset (Fin m))))
        nlinarith [hforward i0, hle]
      have hs_pos : 0 < ∑ i : Fin m, d i := by
        simpa [hmass] using hs_pos_forward
      have hforward_eventually :
          ∀ᶠ t in 𝓝[>] (0 : ℝ),
            ∀ i : Fin m, 0 < Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ)) i := by
        simpa [Filter.Eventually, Set.setOf_forall] using
          (Filter.iInter_mem.2 fun i : Fin m ↦ by
            have hcont :
                Continuous fun t : ℝ ↦
                  Matrix.mulVec K (f + t • EuclideanSpace.single j (1 : ℝ)) i := by
              continuity
            have hmem :
                Matrix.mulVec K
                    (f + (0 : ℝ) • EuclideanSpace.single j (1 : ℝ))
                    i ∈ Set.Ioi (0 : ℝ) := by
              simpa using hforward i
            exact
              ((hcont.continuousAt.eventually
                (IsOpen.mem_nhds isOpen_Ioi hmem)).filter_mono inf_le_left))
      have hden_eventually :
          ∀ᶠ t in 𝓝[>] (0 : ℝ),
            0 < ∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j := by
        have hcont :
            Continuous fun t : ℝ ↦ ∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j := by
          continuity
        have hmem :
            (∑ i : Fin m, d i + (0 : ℝ) * RichardsonLucy.columnSum K j) ∈ Set.Ioi (0 : ℝ) := by
          simpa using hs_pos
        exact
          ((hcont.continuousAt.eventually
            (IsOpen.mem_nhds isOpen_Ioi hmem)).filter_mono inf_le_left)
      have hpos_eventually : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := by
        exact self_mem_nhdsWithin
      obtain ⟨t, ht_pos, hden_t, hforward_t⟩ :=
        (hpos_eventually.and <| hden_eventually.and hforward_eventually).exists
      have hcoord_t : 0 ≤ f j + t := by
        nlinarith [hf_nonneg j, ht_pos]
      let scale : ℝ :=
        (∑ i : Fin m, d i) / (∑ i : Fin m, d i + t * RichardsonLucy.columnSum K j)
      let y : EuclideanSpace ℝ (Fin n) :=
        scale • (f + t • EuclideanSpace.single j (1 : ℝ))
      have hy_mem : y ∈ logLikelihoodConstraintSet K d := by
        simpa [y, scale] using
          scaledSinglePerturb_mem_logLikelihoodConstraintSet
            K d f hf_mem j t hs_pos hden_t hcoord_t hforward_t
      have hscale_pos : 0 < scale := by
        exact div_pos hs_pos hden_t
      have hdisp :
          y - f =
            (scale * t) • EuclideanSpace.single j (1 : ℝ) + (scale - 1) • f := by
        ext k
        by_cases hk : k = j
        · subst hk
          simp [y, scale, EuclideanSpace.single, sub_eq_add_neg]
          ring
        · simp [y, scale, EuclideanSpace.single, hk, sub_eq_add_neg]
          ring
      have hinner_f :
          inner ℝ (gradient (negLogLikelihood K d) f) f = 0 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simpa [dotProduct, mul_comm] using hsum_zero
      have hinner_nonneg :
          0 ≤ inner ℝ (gradient (negLogLikelihood K d) f) (y - f) :=
        inner_gradient_sub_nonneg_of_isLocalMinOn
          (negLogLikelihood K d)
          (convex_logLikelihoodConstraintSet K d)
          hf_mem
          hmin
          hJ_diff
          hy_mem
      rw [hdisp, inner_add_right, inner_smul_right, inner_smul_right, hinner_f] at hinner_nonneg
      have hprod_nonneg : 0 ≤ scale * t * gradient (negLogLikelihood K d) f j := by
        simpa [gradient_apply_eq_fderiv_single, EuclideanSpace.inner_single_right,
          mul_comm, mul_left_comm, mul_assoc] using
          hinner_nonneg
      by_contra hgrad_neg
      have hgrad_neg' : gradient (negLogLikelihood K d) f j < 0 := lt_of_not_ge hgrad_neg
      have hscale_t_pos : 0 < scale * t := mul_pos hscale_pos ht_pos
      have hprod_neg : scale * t * gradient (negLogLikelihood K d) f j < 0 := by
        exact mul_neg_of_pos_of_neg hscale_t_pos hgrad_neg'
      linarith
  have hcomp :
      ∀ j : Fin n, f j * gradient (negLogLikelihood K d) f j = 0 := by
    have hterm_nonneg :
        ∀ j : Fin n, 0 ≤ f j * gradient (negLogLikelihood K d) f j := by
      intro j
      exact mul_nonneg (hf_nonneg j) (hgrad_nonneg j)
    have hzero_all :
        ∀ j : Fin n, f j * gradient (negLogLikelihood K d) f j = 0 := by
      simpa using
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ hterm_nonneg j)).mp hsum_zero
    exact hzero_all
  refine NonnegativeOrthant.ofConditions ?_ hgrad_nonneg hcomp
  simpa [NonnegativeOrthant.mem_feasibleSet] using hf_feasible

/-- Exercise 9.14 (2). Since `J(f) = -ℓ(f; d)` from `(9.44)` is convex on the
nonnegative orthant, any critical point for `J` is a minimizer on
`NonnegativeOrthant.feasibleSet n`. This is the source-facing specialization of
`NonnegativeOrthant.isMinOn_of_isCriticalPoint_of_convexOn` to
`PoissonInverse.negLogLikelihood K d`. -/
theorem isMinOn_negLogLikelihood_of_isCriticalPoint
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n))
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ (negLogLikelihood K d) x)
    (hJ_convex :
      ConvexOn ℝ (NonnegativeOrthant.feasibleSet n) (negLogLikelihood K d))
    (hcrit : NonnegativeOrthant.IsCriticalPoint (negLogLikelihood K d) f) :
    IsMinOn (negLogLikelihood K d) (NonnegativeOrthant.feasibleSet n) f := by
  -- This is exactly Remark 9.10 specialized to `PoissonInverse.negLogLikelihood`.
  exact NonnegativeOrthant.isMinOn_of_isCriticalPoint_of_convexOn hJ_diff hJ_convex hcrit

end PoissonInverse

/- Companion owner for the Chapter 9 likelihood `(9.41)` used in clause `(1)`. -/
#check PoissonInverse.logLikelihood

/- Companion owner for the constraint set used in the clause `(1)`
maximization problem. -/
#check PoissonInverse.logLikelihoodConstraintSet

/- Companion owner for the negative log-likelihood objective `J(f) = -ℓ(f; d)`
from `(9.44)`. -/
#check PoissonInverse.negLogLikelihood

/- Companion anchor for the target notion in clause `(1)`. -/
#check NonnegativeOrthant.IsCriticalPoint

/- Companion anchor for the equality constraint `(9.43)` on the Chapter 9
constraint set used in clause `(1)`. -/
#check PoissonInverse.sum_mulVec_eq_sum_data_of_mem_logLikelihoodConstraintSet
