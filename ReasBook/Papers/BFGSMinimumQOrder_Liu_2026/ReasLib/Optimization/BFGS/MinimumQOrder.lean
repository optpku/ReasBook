module

public import ReasLib.Analysis.Convex.Hessian
public import ReasLib.Analysis.QuadraticTail
public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Convergence
public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Interpolation
public import ReasLib.Optimization.BFGS.PlanarRealization
public import ReasLib.Optimization.BFGS.Scaling
public import ReasLib.Optimization.LineSearchConvergence

public section

open scoped ContDiff EuclideanSpace Matrix.Norms.L2Operator Topology

namespace BFGS

/-- The proof-only properties of a localized smooth strongly convex objective and an
identity-initialized, nonterminating exact-line-search BFGS run of Q-order one. -/
structure IsOrderOneExample {n : ℕ} (ε R : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (B : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (α : ℕ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ F
  strongConvex : ∃ m > 0, StrongConvexOn Set.univ m F
  smoothQuadraticTail :
    ContDiff ℝ ∞ (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
  compactSupportQuadraticTail :
    HasCompactSupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
  localized :
    tsupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∪ {x₀} ⊆
      Metric.ball 0 R
  hessianClose : ∃ η : ℝ, 0 ≤ η ∧ η < ε ∧
    ∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian F z - 1‖ ≤ η
  uniqueMinimizer : ∀ z : EuclideanSpace ℝ (Fin n), IsMinOn F Set.univ z ↔ z = 0
  hessianAtZero : ConvexAnalysis.hessian F 0 = 1
  initial : x 0 = x₀
  trajectory : IsTrajectory F (1 : Matrix (Fin n) (Fin n) ℝ) x B α
  nonterminating : ∀ k, x k ≠ 0
  superlinear : QConvergence.IsSuperlinear x 0
  orderEqOne : QConvergence.order x 0 = (1 : ENNReal)

namespace IsOrderOneExample

set_option linter.defProp false in
/-- Construct the order-one BFGS example predicate from its objective, run, and rate
conditions. -/
def ofConditions {n : ℕ} {ε R : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {α : ℕ → ℝ}
    (smooth : ContDiff ℝ ∞ F)
    (strongConvex : ∃ m > 0, StrongConvexOn Set.univ m F)
    (smoothQuadraticTail :
      ContDiff ℝ ∞ (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))
    (compactSupportQuadraticTail :
      HasCompactSupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))
    (localized :
      tsupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∪ {x₀} ⊆
        Metric.ball 0 R)
    (hessianClose : ∃ η : ℝ, 0 ≤ η ∧ η < ε ∧
      ∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian F z - 1‖ ≤ η)
    (uniqueMinimizer : ∀ z : EuclideanSpace ℝ (Fin n), IsMinOn F Set.univ z ↔ z = 0)
    (hessianAtZero : ConvexAnalysis.hessian F 0 = 1)
    (initial : x 0 = x₀)
    (trajectory : IsTrajectory F (1 : Matrix (Fin n) (Fin n) ℝ) x B α)
    (nonterminating : ∀ k, x k ≠ 0)
    (superlinear : QConvergence.IsSuperlinear x 0)
    (orderEqOne : QConvergence.order x 0 = (1 : ENNReal)) :
    IsOrderOneExample ε R F x₀ x B α :=
  { smooth := smooth
    strongConvex := strongConvex
    smoothQuadraticTail := smoothQuadraticTail
    compactSupportQuadraticTail := compactSupportQuadraticTail
    localized := localized
    hessianClose := hessianClose
    uniqueMinimizer := uniqueMinimizer
    hessianAtZero := hessianAtZero
    initial := initial
    trajectory := trajectory
    nonterminating := nonterminating
    superlinear := superlinear
    orderEqOne := orderEqOne }

/-- BFGS.IsOrderOneExample.objective_spec

The objective-facing conditions of an order-one BFGS example. -/
theorem objective_spec {n : ℕ} {ε R : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {α : ℕ → ℝ} (h : IsOrderOneExample ε R F x₀ x B α) :
    ContDiff ℝ ∞ F ∧
      (∃ m > 0, StrongConvexOn Set.univ m F) ∧
      ContDiff ℝ ∞ (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∧
      HasCompactSupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∧
      tsupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∪ {x₀} ⊆
        Metric.ball 0 R ∧
      (∃ η : ℝ, 0 ≤ η ∧ η < ε ∧
        ∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian F z - 1‖ ≤ η) ∧
      (∀ z : EuclideanSpace ℝ (Fin n), IsMinOn F Set.univ z ↔ z = 0) ∧
      ConvexAnalysis.hessian F 0 = 1 := by
  -- Each objective condition is stored directly in the bundled example.
  exact ⟨h.smooth, h.strongConvex, h.smoothQuadraticTail,
    h.compactSupportQuadraticTail, h.localized, h.hessianClose,
    h.uniqueMinimizer, h.hessianAtZero⟩

/-- The initialization, trajectory, nontermination, convergence, and positive-definiteness
conditions of an order-one BFGS example. -/
theorem run_spec {n : ℕ} {ε R : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {α : ℕ → ℝ} (h : IsOrderOneExample ε R F x₀ x B α) :
    x 0 = x₀ ∧
      IsTrajectory F (1 : Matrix (Fin n) (Fin n) ℝ) x B α ∧
      (∀ k, x k ≠ 0) ∧
      Filter.Tendsto x Filter.atTop (𝓝 0) ∧
      ∀ k, (B k).PosDef := by
  -- The convergence and definiteness clauses follow from the stored rate and trajectory.
  exact ⟨h.initial, h.trajectory, h.nonterminating,
    (QConvergence.isSuperlinear_iff x 0).mp h.superlinear |>.1,
    h.trajectory.posDef⟩

/-- The Q-superlinear and exact Q-order conditions of an order-one BFGS example. -/
theorem rate_spec {n : ℕ} {ε R : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {α : ℕ → ℝ} (h : IsOrderOneExample ε R F x₀ x B α) :
    QConvergence.IsSuperlinear x 0 ∧ QConvergence.order x 0 = (1 : ENNReal) := by
  -- Both rate statements are fields of the example predicate.
  exact ⟨h.superlinear, h.orderEqOne⟩

end IsOrderOneExample

/-- Every positive tolerance admits a
smaller contraction threshold whose inverse perturbation bound remains below it. -/
private theorem existsConjugateThreshold {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ 0 ≤ θ / (1 - θ) ∧ θ / (1 - θ) < ε := by
  let θ : ℝ := ε / (4 * (1 + ε))
  have hθ_pos : 0 < θ := by
    dsimp only [θ]
    positivity
  have hθ_lt_half : θ < 1 / 2 := by
    dsimp only [θ]
    have hdenom : 0 < 4 * (1 + ε) := by positivity
    rw [div_lt_iff₀ hdenom]
    nlinarith
  have hHalfLtOne : (1 / 2 : ℝ) < 1 := by norm_num
  have hθ_lt_one : θ < 1 := hθ_lt_half.trans hHalfLtOne
  have hη_nonneg : 0 ≤ θ / (1 - θ) := by positivity
  have hη_lt : θ / (1 - θ) < ε := by
    rw [div_lt_iff₀ (sub_pos.mpr hθ_lt_one)]
    dsimp only [θ]
    have hdenom : 0 < 4 * (1 + ε) := by positivity
    field_simp [hdenom.ne']
    nlinarith
  exact ⟨θ, hθ_pos, hθ_lt_half, hη_nonneg, hη_lt⟩

/-- A positive interpolation constant
and threshold admit a sufficiently small alternating-scale parameter. -/
private theorem existsInterpolationScale {C θ : ℝ} (hC : 0 < C) (hθ : 0 < θ) :
    ∃ σ : ℝ, σ ∈ Set.Ioo 0 1 ∧ C * σ < θ := by
  let σ : ℝ := θ / (2 * (C + θ))
  have hdenom : 0 < 2 * (C + θ) := by positivity
  have hσ_pos : 0 < σ := by
    dsimp only [σ]
    positivity
  have hσ_lt_one : σ < 1 := by
    dsimp only [σ]
    rw [div_lt_iff₀ hdenom]
    nlinarith
  have hCσ_lt : C * σ < θ := by
    have hQuotientLt : C * θ / (2 * (C + θ)) < θ := by
      rw [div_lt_iff₀ hdenom]
      nlinarith
    calc
      C * σ = C * θ / (2 * (C + θ)) := by
        dsimp only [σ]
        rw [mul_div_assoc]
      _ < θ := hQuotientLt
  exact ⟨σ, ⟨hσ_pos, hσ_lt_one⟩, hCσ_lt⟩

/-- The first two coordinate vectors in
an ambient Euclidean space. -/
private noncomputable def planarCoordinateFamily (n : ℕ) (h_n : 2 ≤ n) :
    Fin 2 → EuclideanSpace ℝ (Fin n) := fun i ↦
  EuclideanSpace.basisFun (Fin n) ℝ (Fin.castLE h_n i)

/-- The linear map sending the standard
planar basis to the first two ambient coordinate vectors. -/
private noncomputable def planarCoordinateLinearMap (n : ℕ) (h_n : 2 ≤ n) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Finsupp.linearCombination ℝ (planarCoordinateFamily n h_n)).comp
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.repr.toLinearMap

/-- The first two coordinate vectors
form an orthonormal family. -/
private theorem planarCoordinateFamily_orthonormal (n : ℕ) (h_n : 2 ≤ n) :
    Orthonormal ℝ (planarCoordinateFamily n h_n) := by
  -- Restrict the ambient standard orthonormal basis along the coordinate inclusion.
  exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.comp
    (Fin.castLE h_n) (Fin.castLE_injective h_n)

/-- The planar coordinate map preserves
the Euclidean norm. -/
private theorem planarCoordinateLinearMap_norm (n : ℕ) (h_n : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖planarCoordinateLinearMap n h_n x‖ = ‖x‖ := by
  -- Expand both vectors in the same coefficients and compare their self-inner-products.
  let c : Fin 2 →₀ ℝ := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.repr x
  have hImage : planarCoordinateLinearMap n h_n x =
      Finsupp.linearCombination ℝ (planarCoordinateFamily n h_n) c := by
    rfl
  have hSource : Finsupp.linearCombination ℝ
      (EuclideanSpace.basisFun (Fin 2) ℝ) c = x :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearCombination_repr x
  have hImageInner : inner ℝ (planarCoordinateLinearMap n h_n x)
      (planarCoordinateLinearMap n h_n x) =
        c.sum fun i y ↦ (starRingEnd ℝ) y * c i := by
    rw [hImage]
    exact (planarCoordinateFamily_orthonormal n h_n).inner_finsupp_eq_sum_left c c
  have hSourceInner : inner ℝ x x =
      c.sum fun i y ↦ (starRingEnd ℝ) y * c i := by
    have horth := (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal
      |>.inner_finsupp_eq_sum_left c c
    rw [hSource] at horth
    exact horth
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    hImageInner, hSourceInner]

/-- The canonical isometric embedding
into the first two ambient coordinates. -/
private noncomputable def planarLinearIsometry (n : ℕ) (h_n : 2 ≤ n) :
    EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  { toLinearMap := planarCoordinateLinearMap n h_n
    norm_map' := planarCoordinateLinearMap_norm n h_n }

/-- Adjacent terms of an
alternating-scale sequence satisfy the pre-step inner-product identity. -/
private theorem PlanarGradient.IsAlternatingScale.preStep
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : PlanarGradient.IsAlternatingScale σ g δ a b) (k : ℕ) :
    inner ℝ (g (k + 1) - g k) (g (k + 1)) =
      inner ℝ (g (k + 1))
        (PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k)) := by
  -- The explicit first two vectors establish the base of the recurrence invariant.
  induction k with
  | zero =>
      let gZero : EuclideanSpace ℝ (Fin 2) := !₂[a, 0]
      let gOne : EuclideanSpace ℝ (Fin 2) := !₂[0, b]
      have hZeroNorm : ‖gZero‖ = a := by
        dsimp only [gZero]
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs,
          abs_of_pos h.aPos]
      have hOneNorm : ‖gOne‖ = b := by
        dsimp only [gOne]
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs,
          abs_of_pos h.bPos]
      have hOrthogonal : inner ℝ gZero gOne = 0 := by
        dsimp only [gZero, gOne]
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
      have hPerturbationInner :
          inner ℝ gOne
              (PlanarGradient.perturbation EuclideanPlane.orientation gZero b) =
            b ^ 2 := by
        rw [PlanarGradient.perturbation_apply, inner_smul_right,
          PlanarGradient.tangent_apply,
          EuclideanPlane.orientation.inner_rightAngleRotation_right,
          EuclideanPlane.orientation.areaForm_swap]
        simp only [neg_neg]
        calc
          b * EuclideanPlane.orientation.areaForm (NormedSpace.normalize gZero) gOne =
              b * EuclideanPlane.orientation.areaForm (NormedSpace.normalize gZero)
                (‖gOne‖ • NormedSpace.normalize gOne) := by
            rw [NormedSpace.norm_smul_normalize]
          _ = b * (‖gOne‖ * EuclideanPlane.orientation.areaForm
                (NormedSpace.normalize gZero) (NormedSpace.normalize gOne)) := by
            rw [map_smul]
            rfl
          _ = b ^ 2 := by
            rw [hOneNorm,
              EuclideanPlane.standardAreaForm_apply, NormedSpace.normalize,
              hZeroNorm, NormedSpace.normalize, hOneNorm]
            dsimp only [gZero, gOne]
            simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
              Matrix.cons_val_one, mul_zero, sub_zero]
            field_simp [h.aPos.ne', h.bPos.ne', abs_of_pos h.aPos, abs_of_pos h.bPos]
      have hInitial : inner ℝ (gOne - gZero) gOne =
          inner ℝ gOne (PlanarGradient.perturbation EuclideanPlane.orientation gZero b) := by
        calc
          inner ℝ (gOne - gZero) gOne = ‖gOne‖ ^ 2 - inner ℝ gZero gOne := by
            rw [inner_sub_left, real_inner_self_eq_norm_sq]
          _ = b ^ 2 := by rw [hOneNorm, hOrthogonal, sub_zero]
          _ = inner ℝ gOne
              (PlanarGradient.perturbation EuclideanPlane.orientation gZero b) :=
            hPerturbationInner.symm
      have hgZero : g 0 = gZero := by
        apply WithLp.ofLp_injective 2
        exact h.initialZero
      have hgOne : g 1 = gOne := by
        apply WithLp.ofLp_injective 2
        exact h.initialOne
      have hδZero : δ 0 = b := h.deltaZero
      have hleft : inner ℝ (g 1 - g 0) (g 1) =
          inner ℝ (gOne - gZero) gOne := by
        exact congrArg₂ (inner ℝ) (congrArg₂ (· - ·) hgOne hgZero) hgOne
      have hperturbation :
          PlanarGradient.perturbation EuclideanPlane.orientation (g 0) (δ 0) =
            PlanarGradient.perturbation EuclideanPlane.orientation gZero b := by
        exact congrArg₂ (PlanarGradient.perturbation EuclideanPlane.orientation)
          hgZero hδZero
      have hright : inner ℝ (g 1)
          (PlanarGradient.perturbation EuclideanPlane.orientation (g 0) (δ 0)) =
            inner ℝ gOne
              (PlanarGradient.perturbation EuclideanPlane.orientation gZero b) := by
        exact congrArg₂ (inner ℝ) hgOne hperturbation
      simpa only [Nat.zero_add] using hleft.trans (hInitial.trans hright.symm)
  | succ k ih =>
      have hDistinct : g (k + 1) ≠ g k := by
        intro heq
        have hDrop := h.radiusStrictAnti (Nat.lt_succ_self k)
        simp only [Nat.succ_eq_add_one] at hDrop
        exact hDrop.ne (congrArg norm heq)
      have hRecurrence : g (k + 2) = PlanarGradient.next EuclideanPlane.orientation
          (g k) (g (k + 1)) (δ (k + 1)) := by
        have hpred : k + 1 - 1 = k := by omega
        simpa only [hpred] using h.recurrence (k + 1) (Nat.succ_pos k)
      have hScale : PlanarGradient.scale EuclideanPlane.orientation
          (g k) (g (k + 1)) (δ (k + 1)) ≠ 0 := by
        intro hScaleZero
        apply h.nonzero (k + 2)
        rw [hRecurrence, PlanarGradient.next_apply, hScaleZero, zero_smul]
      have hOrthogonal := PlanarGradient.next_candidate_orthogonal
        EuclideanPlane.orientation (g k) (g (k + 1)) (δ k) (δ (k + 1))
        (PlanarGradient.perturbation EuclideanPlane.orientation
          (PlanarGradient.next EuclideanPlane.orientation (g k) (g (k + 1))
            (δ (k + 1))) 0)
        (h.nonzero k) (h.nonzero (k + 1)) hDistinct ih hScale
        (PlanarGradient.inner_perturbation EuclideanPlane.orientation
          (PlanarGradient.next EuclideanPlane.orientation (g k) (g (k + 1))
            (δ (k + 1))) 0)
      rw [PlanarGradient.perturbation_apply, zero_smul, add_zero,
        PlanarGradient.candidate_apply, inner_sub_right, inner_add_right] at hOrthogonal
      rw [show k + 1 + 1 = k + 2 by omega, hRecurrence, inner_sub_left,
        real_inner_comm
          (PlanarGradient.next EuclideanPlane.orientation (g k) (g (k + 1))
            (δ (k + 1))) (g (k + 1))]
      linarith

/-- An alternating-scale recurrence
has nonzero scale at every positive-index update. -/
private theorem PlanarGradient.IsAlternatingScale.scaleNonzero
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : PlanarGradient.IsAlternatingScale σ g δ a b) (k : ℕ) :
    PlanarGradient.scale EuclideanPlane.orientation (g k) (g (k + 1)) (δ (k + 1)) ≠ 0 := by
  -- A zero recurrence scale would make the next stored gradient vanish.
  intro hScale
  apply h.nonzero (k + 2)
  have hRecurrence : g (k + 2) = PlanarGradient.next EuclideanPlane.orientation
      (g k) (g (k + 1)) (δ (k + 1)) := by
    have hpred : k + 1 - 1 = k := by omega
    simpa only [hpred] using h.recurrence (k + 1) (Nat.succ_pos k)
  rw [hRecurrence, PlanarGradient.next_apply, hScale, zero_smul]

/-- The candidate perturbation changes
the gradient norm by at most the fixed alternating-scale factor. -/
private theorem PlanarGradient.IsAlternatingScale.candidateNormBounds
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : PlanarGradient.IsAlternatingScale σ g δ a b) (k : ℕ) :
    ‖g k‖ ≤ ‖PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)‖ ∧
      ‖PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)‖ ≤
        (1 + σ) * ‖g k‖ := by
  have hnorm_pos : 0 < ‖g k‖ := norm_pos_iff.mpr (h.nonzero k)
  have hδ_bound : |δ k| ≤ σ * ‖g k‖ :=
    (div_le_iff₀ hnorm_pos).mp (h.perturbationRatioLe k)
  have hPythagoras :
      ‖PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)‖ ^ 2 =
        ‖g k‖ ^ 2 +
          ‖PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k)‖ ^ 2 := by
    rw [PlanarGradient.candidate_apply]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
        (PlanarGradient.inner_perturbation EuclideanPlane.orientation (g k) (δ k))
  constructor
  · nlinarith [sq_nonneg
      ‖PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k)‖,
      norm_nonneg (PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k))]
  · rw [PlanarGradient.candidate_apply]
    calc
      ‖g k + PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k)‖ ≤
          ‖g k‖ + ‖PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k)‖ :=
        norm_add_le _ _
      _ = ‖g k‖ + |δ k| := by
        rw [PlanarGradient.norm_perturbation EuclideanPlane.orientation (δ k) (h.nonzero k)]
      _ ≤ ‖g k‖ + σ * ‖g k‖ := add_le_add_right hδ_bound _
      _ = (1 + σ) * ‖g k‖ := by ring

/-- The first candidate displacement
is a negative positive multiple of the first gradient. -/
private theorem PlanarGradient.IsAlternatingScale.candidateInitialStep
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : PlanarGradient.IsAlternatingScale σ g δ a b) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      PlanarGradient.candidate EuclideanPlane.orientation (g 1) (δ 1) -
          PlanarGradient.candidate EuclideanPlane.orientation (g 0) (δ 0) =
        (-β₀) • g 0 := by
  let gZero : EuclideanSpace ℝ (Fin 2) := !₂[a, 0]
  let gOne : EuclideanSpace ℝ (Fin 2) := !₂[0, b]
  let β₀ : ℝ := 1 + δ 1 / a
  have hδ_lower : -(a / 2) < δ 1 := (abs_lt.mp h.deltaOneLt).1
  have hβ₀ : 0 < β₀ := by
    have ha_ne : a ≠ 0 := h.aPos.ne'
    have hnum : 0 < a + δ 1 := by nlinarith [h.aPos]
    have hformula : β₀ = (a + δ 1) / a := by
      dsimp only [β₀]
      field_simp [ha_ne]
    rw [hformula]
    exact div_pos hnum h.aPos
  refine ⟨β₀, hβ₀, ?_⟩
  -- Evaluate the quarter-turn on the two explicit initial coordinate vectors.
  have hZeroNorm : ‖gZero‖ = a := by
    dsimp only [gZero]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs,
      abs_of_pos h.aPos]
  have hOneNorm : ‖gOne‖ = b := by
    dsimp only [gOne]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs,
      abs_of_pos h.bPos]
  have hRotateZero : EuclideanPlane.orientation.rightAngleRotation
      (NormedSpace.normalize gZero) =
        (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · calc
        _ = inner ℝ (EuclideanPlane.orientation.rightAngleRotation
              (NormedSpace.normalize gZero))
            (EuclideanSpace.basisFun (Fin 2) ℝ 0) :=
          (EuclideanSpace.inner_basisFun_real (Fin 2) _ 0).symm
        _ = EuclideanPlane.orientation.areaForm (NormedSpace.normalize gZero)
            (EuclideanSpace.basisFun (Fin 2) ℝ 0) :=
          EuclideanPlane.orientation.inner_rightAngleRotation_left _ _
        _ = 0 := by
          simp [EuclideanPlane.standardAreaForm_apply, NormedSpace.normalize,
            hZeroNorm, gZero]
        _ = _ := by simp
    · calc
        _ = inner ℝ (EuclideanPlane.orientation.rightAngleRotation
              (NormedSpace.normalize gZero))
            (EuclideanSpace.basisFun (Fin 2) ℝ 1) :=
          (EuclideanSpace.inner_basisFun_real (Fin 2) _ 1).symm
        _ = EuclideanPlane.orientation.areaForm (NormedSpace.normalize gZero)
            (EuclideanSpace.basisFun (Fin 2) ℝ 1) :=
          EuclideanPlane.orientation.inner_rightAngleRotation_left _ _
        _ = 1 := by
          simp [EuclideanPlane.standardAreaForm_apply, NormedSpace.normalize,
            hZeroNorm, gZero, h.aPos.ne']
        _ = _ := by simp
  have hRotateOne : EuclideanPlane.orientation.rightAngleRotation
      (NormedSpace.normalize gOne) =
        (!₂[-(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · calc
        _ = inner ℝ (EuclideanPlane.orientation.rightAngleRotation
              (NormedSpace.normalize gOne))
            (EuclideanSpace.basisFun (Fin 2) ℝ 0) :=
          (EuclideanSpace.inner_basisFun_real (Fin 2) _ 0).symm
        _ = EuclideanPlane.orientation.areaForm (NormedSpace.normalize gOne)
            (EuclideanSpace.basisFun (Fin 2) ℝ 0) :=
          EuclideanPlane.orientation.inner_rightAngleRotation_left _ _
        _ = -1 := by
          simp [EuclideanPlane.standardAreaForm_apply, NormedSpace.normalize,
            hOneNorm, gOne, h.bPos.ne']
        _ = _ := by simp
    · calc
        _ = inner ℝ (EuclideanPlane.orientation.rightAngleRotation
              (NormedSpace.normalize gOne))
            (EuclideanSpace.basisFun (Fin 2) ℝ 1) :=
          (EuclideanSpace.inner_basisFun_real (Fin 2) _ 1).symm
        _ = EuclideanPlane.orientation.areaForm (NormedSpace.normalize gOne)
            (EuclideanSpace.basisFun (Fin 2) ℝ 1) :=
          EuclideanPlane.orientation.inner_rightAngleRotation_left _ _
        _ = 0 := by
          simp [EuclideanPlane.standardAreaForm_apply, NormedSpace.normalize,
            hOneNorm, gOne]
        _ = _ := by simp
  have hExplicit :
      PlanarGradient.candidate EuclideanPlane.orientation gOne (δ 1) -
          PlanarGradient.candidate EuclideanPlane.orientation gZero b =
        (-β₀) • gZero := by
    apply WithLp.ofLp_injective 2
    funext i
    rw [PlanarGradient.candidate_apply, PlanarGradient.candidate_apply,
      PlanarGradient.perturbation_apply, PlanarGradient.perturbation_apply,
      PlanarGradient.tangent_apply, PlanarGradient.tangent_apply, hRotateOne, hRotateZero]
    fin_cases i
    · simp [gZero, gOne, β₀]
      field_simp [h.aPos.ne']
      ring
    · simp [gZero, gOne, β₀]
  have hgZero : g 0 = gZero := by
    apply WithLp.ofLp_injective 2
    exact h.initialZero
  have hgOne : g 1 = gOne := by
    apply WithLp.ofLp_injective 2
    exact h.initialOne
  have hδZero : δ 0 = b := h.deltaZero
  have hCandidateZero :
      PlanarGradient.candidate EuclideanPlane.orientation (g 0) (δ 0) =
        PlanarGradient.candidate EuclideanPlane.orientation gZero b := by
    exact congrArg₂ (PlanarGradient.candidate EuclideanPlane.orientation) hgZero hδZero
  have hCandidateOne :
      PlanarGradient.candidate EuclideanPlane.orientation (g 1) (δ 1) =
        PlanarGradient.candidate EuclideanPlane.orientation gOne (δ 1) := by
    exact congrArg₂ (PlanarGradient.candidate EuclideanPlane.orientation) hgOne rfl
  calc
    PlanarGradient.candidate EuclideanPlane.orientation (g 1) (δ 1) -
        PlanarGradient.candidate EuclideanPlane.orientation (g 0) (δ 0) =
      PlanarGradient.candidate EuclideanPlane.orientation gOne (δ 1) -
        PlanarGradient.candidate EuclideanPlane.orientation gZero b :=
      congrArg₂ (· - ·) hCandidateOne hCandidateZero
    _ = (-β₀) • gZero := hExplicit
    _ = (-β₀) • g 0 := congrArg (fun z ↦ (-β₀) • z) hgZero.symm

/-- An isometric embedding of the alternating planar candidates is realized by an
identity-initialized exact-line-search BFGS trajectory. -/
private theorem PlanarGradient.IsAlternatingScale.existsTrajectory_of_embeddedCandidates
    {n : ℕ} {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : PlanarGradient.IsAlternatingScale σ g δ a b)
    (ι : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ)
    (hF : Differentiable ℝ F) (hm : 0 < m)
    (hStrong : StrongConvexOn Set.univ m F)
    (hGradient : ∀ k, gradient F
      (ι (PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k))) = ι (g k)) :
    ∃ (B : ℕ → Matrix (Fin n) (Fin n) ℝ) (α : ℕ → ℝ),
      IsTrajectory F (1 : Matrix (Fin n) (Fin n) ℝ)
        (fun k ↦ ι (PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k))) B α := by
  let u : ℕ → EuclideanSpace ℝ (Fin 2) := fun k ↦
    PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ ι (u k)
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.range ι.toLinearMap
  have hDim : Module.finrank ℝ V = 2 := by
    dsimp only [V]
    rw [LinearMap.finrank_range_of_inj ι.injective]
    simp
  have hDistinct : Function.Injective x := by
    intro i j hij
    have hGradientEq := congrArg (gradient F) hij
    rw [hGradient i, hGradient j] at hGradientEq
    have hgEq : g i = g j := ι.injective hGradientEq
    exact h.radiusStrictAnti.injective (congrArg norm hgEq)
  have hPointMem (k : ℕ) : x k ∈ V := by
    exact ⟨u k, rfl⟩
  have hGradientMem (k : ℕ) : gradient F (x k) ∈ V := by
    rw [hGradient k]
    exact ⟨g k, rfl⟩
  have hPlaneOrthogonal (k : ℕ) :
      inner ℝ (g (k + 1)) (u (k + 1) - u k) = 0 := by
    have hPre := preStep h k
    rw [inner_sub_left, ← real_inner_comm (g k) (g (k + 1))] at hPre
    have hTangent := PlanarGradient.inner_perturbation EuclideanPlane.orientation
      (g (k + 1)) (δ (k + 1))
    dsimp only [u]
    rw [PlanarGradient.candidate_apply, PlanarGradient.candidate_apply,
      inner_sub_right, inner_add_right, inner_add_right]
    linarith
  have hOrthogonal (k : ℕ) :
      inner ℝ (gradient F (x (k + 1))) (x (k + 1) - x k) = 0 := by
    rw [hGradient (k + 1)]
    have hStep : x (k + 1) - x k = ι (u (k + 1) - u k) := by
      simp only [x, map_sub]
    rw [hStep, ι.inner_map_map]
    exact hPlaneOrthogonal k
  have hGradientSpan (k : ℕ) : gradient F (x (k + 2)) ∈
      Submodule.span ℝ {gradient F (x (k + 1)) - gradient F (x k)} := by
    have hAdjacent : g (k + 1) ≠ g k := by
      intro hg
      exact (h.radiusStrictAnti (Nat.lt_succ_self k)).ne (congrArg norm hg)
    have hNext := PlanarGradient.next_mem_span EuclideanPlane.orientation
      (g k) (g (k + 1)) (δ k) (δ (k + 1)) (h.nonzero k) (h.nonzero (k + 1))
      hAdjacent (preStep h k) (scaleNonzero h k)
    have hRecurrence : g (k + 2) = PlanarGradient.next EuclideanPlane.orientation
        (g k) (g (k + 1)) (δ (k + 1)) := by
      have hPred : k + 1 - 1 = k := by omega
      simpa only [hPred] using h.recurrence (k + 1) (Nat.succ_pos k)
    rw [← hRecurrence] at hNext
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hNext
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [hGradient (k + 2), hGradient (k + 1), hGradient k, ← map_sub, ← map_smul]
    exact congrArg ι hc
  have hGradientNe (k : ℕ) : gradient F (x (k + 2)) ≠ 0 := by
    rw [hGradient (k + 2)]
    intro hz
    apply h.nonzero (k + 2)
    apply ι.injective
    simpa only [map_zero] using hz
  obtain ⟨β₀, hβ₀, hInitialPlane⟩ := candidateInitialStep h
  have hInitial : x 1 - x 0 = (-β₀) • gradient F (x 0) := by
    rw [hGradient 0]
    simpa only [x, u, map_sub, map_smul] using congrArg ι hInitialPlane
  -- The abstract rank-two realization theorem now supplies the BFGS matrices and steps.
  obtain ⟨B, α, hRun, _⟩ := existsTrajectory_of_planarRelations V F x m β₀ hDim hF hm
    hStrong hDistinct hPointMem hGradientMem hOrthogonal hGradientSpan hGradientNe hβ₀ hInitial
  exact ⟨B, α, hRun⟩

/-- The candidate sequence associated
to an alternating-scale sequence converges Q-superlinearly to zero. -/
private theorem PlanarGradient.IsAlternatingScale.candidateIsSuperlinear
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : PlanarGradient.IsAlternatingScale σ g δ a b) (hσ : 0 ≤ σ) :
    QConvergence.IsSuperlinear
      (fun k ↦ PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)) 0 := by
  let u : ℕ → EuclideanSpace ℝ (Fin 2) := fun k ↦
    PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)
  have hBounds (k : ℕ) : ‖g k‖ ≤ ‖u k‖ ∧ ‖u k‖ ≤ (1 + σ) * ‖g k‖ :=
    candidateNormBounds h k
  have hA_pos : 0 < 1 + σ := by linarith
  have hu_pos (k : ℕ) : 0 < ‖u k‖ :=
    (norm_pos_iff.mpr (h.nonzero k)).trans_le (hBounds k).1
  rw [QConvergence.isSuperlinear_iff_ratio]
  constructor
  · -- The uniform upper comparison transfers convergence of the radii.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hUpper : Filter.Tendsto (fun k ↦ (1 + σ) * ‖g k‖)
        Filter.atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul h.radiusTendsto)
    have hUpperEventually : ∀ᶠ k in Filter.atTop, ‖u k - 0‖ ≤ (1 + σ) * ‖g k‖ := by
      filter_upwards [] with k
      simpa only [sub_zero] using (hBounds k).2
    apply squeeze_zero' (Filter.Eventually.of_forall (fun k ↦ norm_nonneg (u k - 0)))
      hUpperEventually hUpper
  constructor
  · exact Filter.Eventually.of_forall fun k huZero ↦
      (ne_of_gt (hu_pos k)) (congrArg norm huZero |>.trans norm_zero)
  · -- Divide the upper next-step comparison by the lower current-step comparison.
    have hRatioBound (k : ℕ) :
        ‖u (k + 1)‖ / ‖u k‖ ≤ (1 + σ) * (‖g (k + 1)‖ / ‖g k‖) := by
      rw [div_le_iff₀ (hu_pos k)]
      calc
        ‖u (k + 1)‖ ≤ (1 + σ) * ‖g (k + 1)‖ := (hBounds (k + 1)).2
        _ = ((1 + σ) * (‖g (k + 1)‖ / ‖g k‖)) * ‖g k‖ := by
          field_simp [(norm_pos_iff.mpr (h.nonzero k)).ne']
        _ ≤ ((1 + σ) * (‖g (k + 1)‖ / ‖g k‖)) * ‖u k‖ := by
          apply mul_le_mul_of_nonneg_left (hBounds k).1
          positivity
    have hUpperRatio : Filter.Tendsto
        (fun k ↦ (1 + σ) * (‖g (k + 1)‖ / ‖g k‖)) Filter.atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul h.ratioTendsto)
    simpa only [QConvergence.error_apply, sub_zero] using
      squeeze_zero' (Filter.Eventually.of_forall (fun k ↦ div_nonneg
        (norm_nonneg (u (k + 1))) (norm_nonneg (u k))))
        (Filter.Eventually.of_forall hRatioBound) hUpperRatio

/-- Bounded tangential perturbations
preserve the exact Q-order one of an alternating-scale sequence. -/
private theorem PlanarGradient.IsAlternatingScale.candidateOrderEqOne
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : PlanarGradient.IsAlternatingScale σ g δ a b) (hσ : 0 ≤ σ) :
    QConvergence.order
      (fun k ↦ PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)) 0 = 1 := by
  let u : ℕ → EuclideanSpace ℝ (Fin 2) := fun k ↦
    PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)
  have hBounds (k : ℕ) : ‖g k‖ ≤ ‖u k‖ ∧ ‖u k‖ ≤ (1 + σ) * ‖g k‖ :=
    candidateNormBounds h k
  have hA_pos : 0 < 1 + σ := by linarith
  have huSuper : QConvergence.IsSuperlinear u 0 := candidateIsSuperlinear h hσ
  rw [QConvergence.order_eq_one_iff]
  constructor
  · -- Little-o decay supplies the admissible exponent one.
    rw [QConvergence.hasOrderAtLeast_iff]
    rcases (QConvergence.isSuperlinear_iff u 0).mp huSuper with
      ⟨huTendsto, huNonstationary, huLittle⟩
    obtain ⟨C, hC, hBound⟩ := Asymptotics.isBigO_iff'.mp huLittle.isBigO
    refine ⟨huTendsto, huNonstationary, le_rfl, C, hC, ?_⟩
    filter_upwards [hBound] with k hk
    simpa only [Real.norm_eq_abs, abs_of_nonneg, QConvergence.error_apply,
      norm_nonneg, Real.rpow_one] using hk
  · intro p hp huOrder
    rw [QConvergence.hasOrderAtLeast_iff] at huOrder
    rcases huOrder with ⟨_, _, hp_one, C, hC, huBound⟩
    have hgSuper := h.isSuperlinear
    rcases (QConvergence.isSuperlinear_iff g 0).mp hgSuper with
      ⟨hgTendsto, hgNonstationary, _⟩
    have hgBound : ∀ᶠ k in Filter.atTop,
        QConvergence.error g 0 (k + 1) ≤
          (C * (1 + σ) ^ p) * QConvergence.error g 0 k ^ p := by
      filter_upwards [huBound] with k hk
      have hPower : ‖u k‖ ^ p ≤ ((1 + σ) * ‖g k‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) (hBounds k).2 (zero_le_one.trans hp_one)
      calc
        QConvergence.error g 0 (k + 1) = ‖g (k + 1)‖ := by
          rw [QConvergence.error_apply, sub_zero]
        _ ≤ ‖u (k + 1)‖ := (hBounds (k + 1)).1
        _ = QConvergence.error u 0 (k + 1) := by
          rw [QConvergence.error_apply, sub_zero]
        _ ≤ C * QConvergence.error u 0 k ^ p := hk
        _ = C * ‖u k‖ ^ p := by rw [QConvergence.error_apply, sub_zero]
        _ ≤ C * ((1 + σ) * ‖g k‖) ^ p :=
          mul_le_mul_of_nonneg_left hPower hC.le
        _ = (C * (1 + σ) ^ p) * QConvergence.error g 0 k ^ p := by
          rw [Real.mul_rpow hA_pos.le (norm_nonneg (g k)),
            QConvergence.error_apply, sub_zero]
          ring
    have hgOrder : QConvergence.HasOrderAtLeast g 0 p := by
      rw [QConvergence.hasOrderAtLeast_iff]
      refine ⟨hgTendsto, hgNonstationary, hp_one,
        C * (1 + σ) ^ p, ?_, hgBound⟩
      exact mul_pos hC (Real.rpow_pos_of_pos hA_pos p)
    exact (QConvergence.order_eq_one_iff g 0).mp h.order_eq_one |>.2 p hp hgOrder

/-- A linear isometry preserves the
error of a sequence at every index. -/
private theorem QConvergence.error_linearIsometry
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E →ₗᵢ[ℝ] E') (x : ℕ → E) (xStar : E) (k : ℕ) :
    QConvergence.error (fun j ↦ f (x j)) (f xStar) k =
      QConvergence.error x xStar k := by
  -- Move the difference through the linear map and use norm preservation.
  rw [QConvergence.error_apply, QConvergence.error_apply, ← map_sub, f.norm_map]

/-- A linear isometry preserves and
reflects every lower Q-order bound. -/
private theorem QConvergence.hasOrderAtLeast_linearIsometry
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E →ₗᵢ[ℝ] E') (x : ℕ → E) (xStar : E) (p : ℝ) :
    QConvergence.HasOrderAtLeast (fun k ↦ f (x k)) (f xStar) p ↔
      QConvergence.HasOrderAtLeast x xStar p := by
  have hTendsto :
      Filter.Tendsto (fun k ↦ f (x k)) Filter.atTop (𝓝 (f xStar)) ↔
        Filter.Tendsto x Filter.atTop (𝓝 xStar) := by
    constructor
    · intro hImage
      rw [tendsto_iff_norm_sub_tendsto_zero] at hImage
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [← map_sub, f.norm_map] using hImage
    · intro hSource
      rw [tendsto_iff_norm_sub_tendsto_zero] at hSource
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [← map_sub, f.norm_map] using hSource
  have hNe (k : ℕ) : f (x k) ≠ f xStar ↔ x k ≠ xStar := by
    constructor
    · intro hImage hEq
      exact hImage (congrArg f hEq)
    · intro hSource hEq
      exact hSource (f.injective hEq)
  -- All four clauses in the quantitative characterization are unchanged.
  simp only [QConvergence.hasOrderAtLeast_iff, hTendsto, hNe,
    QConvergence.error_linearIsometry]

/-- A linear isometry preserves
Q-superlinear convergence. -/
private theorem QConvergence.isSuperlinear_linearIsometry
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E →ₗᵢ[ℝ] E') (x : ℕ → E) (xStar : E)
    (h : QConvergence.IsSuperlinear x xStar) :
    QConvergence.IsSuperlinear (fun k ↦ f (x k)) (f xStar) := by
  rw [QConvergence.isSuperlinear_iff_ratio] at h ⊢
  rcases h with ⟨hTendsto, hNe, hRatio⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Norm preservation transfers convergence to the embedded limit.
    rw [tendsto_iff_norm_sub_tendsto_zero] at hTendsto ⊢
    simpa only [← map_sub, f.norm_map] using hTendsto
  · filter_upwards [hNe] with k hk
    intro hEq
    exact hk (f.injective hEq)
  · -- The adjacent-error quotient is literally unchanged.
    simpa only [QConvergence.error_linearIsometry] using hRatio

/-- A linear isometry preserves the
totalized Q-order. -/
private theorem QConvergence.order_linearIsometry
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E →ₗᵢ[ℝ] E') (x : ℕ → E) (xStar : E) :
    QConvergence.order (fun k ↦ f (x k)) (f xStar) =
      QConvergence.order x xStar := by
  have hExponents :
      QConvergence.admissibleExponents (fun k ↦ f (x k)) (f xStar) =
        QConvergence.admissibleExponents x xStar := by
    ext p
    rw [QConvergence.mem_admissibleExponents, QConvergence.mem_admissibleExponents,
      QConvergence.hasOrderAtLeast_linearIsometry]
  -- Equal admissible exponent sets have equal extended suprema.
  rw [QConvergence.order_def, QConvergence.order_def, hExponents]

/-- Multiplication by a nonzero
real scalar preserves Q-superlinear convergence. -/
private theorem QConvergence.isSuperlinear_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (xStar : E) (c : ℝ) (hc : c ≠ 0)
    (h : QConvergence.IsSuperlinear x xStar) :
    QConvergence.IsSuperlinear (fun k ↦ c • x k) (c • xStar) := by
  rw [QConvergence.isSuperlinear_iff_ratio] at h ⊢
  rcases h with ⟨hTendsto, hNe, hRatio⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (tendsto_const_smul_iff₀ hc).2 hTendsto
  · filter_upwards [hNe] with k hk
    intro hEq
    exact hk (smul_right_injective E hc hEq)
  · have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
    simpa only [QConvergence.error_smul, mul_div_mul_left _ _ habs] using hRatio

/-- In every dimension at least two, and at every positive accuracy and localization
scale, there is a smooth globally strongly convex localized perturbation of the standard
quadratic whose identity-initialized exact-line-search BFGS trajectory is nonterminating,
Q-superlinear, and has Q-order exactly one. -/
theorem exists_orderOneExample (n : ℕ) (h_n : 2 ≤ n) (ε R : ℝ)
    (hε : 0 < ε) (hR : 0 < R) :
    ∃ (F : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
      (x : ℕ → EuclideanSpace ℝ (Fin n)) (B : ℕ → Matrix (Fin n) (Fin n) ℝ)
      (α : ℕ → ℝ), IsOrderOneExample ε R F x₀ x B α := by
  classical
  -- Choose a Hessian perturbation threshold whose conjugate bound stays below `ε`.
  obtain ⟨θ, hθ_pos, hθ_lt_half, hη_nonneg, hη_lt⟩ :=
    existsConjugateThreshold hε
  have hHalfLtOne : (1 / 2 : ℝ) < 1 := by norm_num
  have hθ_lt_one : θ < 1 := hθ_lt_half.trans hHalfLtOne
  obtain ⟨C, hC, h_interpolate⟩ :=
    PlanarGradient.exists_compactlySupportedInterpolation n h_n
  obtain ⟨σ, hσ, hCσ_lt⟩ := existsInterpolationScale hC hθ_pos
  obtain ⟨g, δ, a, b, hAlt⟩ := PlanarGradient.exists_alternatingScale σ hσ
  -- Embed the planar construction into the first two ambient coordinates.
  let ι := planarLinearIsometry n h_n
  obtain ⟨H, hH_smooth, hH_tail_smooth, hH_tail_compact, hH_support,
      hH_gradient, hH_gradient_zero, hH_hessian_zero, hH_hessian⟩ :=
    h_interpolate ι σ hσ g δ a b hAlt
  have hSup_le : sSup (Set.range (fun k : ℕ ↦ |δ k| / ‖g k‖)) ≤ σ := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact hAlt.perturbationRatioLe k
  have hH_close : ∀ z : EuclideanSpace ℝ (Fin n),
      ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ := by
    intro z
    exact (hH_hessian z).trans_lt
      ((mul_le_mul_of_nonneg_left hSup_le hC.le).trans_lt hCσ_lt) |>.le
  -- The smooth conjugacy interface turns interpolation of `gradient H` into the
  -- required interpolation of the conjugate objective's gradient.
  let F₀ : EuclideanSpace ℝ (Fin n) → ℝ := ConvexAnalysis.conjugate H
  have hConj : QuadraticTail.SmoothConjugateData H θ :=
    QuadraticTail.smoothConjugateData H θ hH_smooth hH_tail_smooth
      hH_tail_compact hH_close hθ_lt_one hH_gradient_zero hH_hessian_zero
  have hF₀Smooth : ContDiff ℝ ∞ F₀ := by
    simpa only [F₀] using hConj.conjugateSmooth
  have hF₀TailSmooth : ContDiff ℝ ∞
      (F₀ - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
    simpa only [F₀] using hConj.conjugateTailSmooth
  have hF₀TailCompact : HasCompactSupport
      (F₀ - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
    simpa only [F₀] using hConj.compactTail
  have hF₀Support :
      tsupport (F₀ - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
        Metric.closedBall 0 (5 * ‖g 0‖ / 4) := by
    have hConjugateSupport :
        tsupport (F₀ - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
          tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
      simpa only [F₀] using hConj.supportSubset
    exact hConjugateSupport.trans hH_support
  let u : ℕ → EuclideanSpace ℝ (Fin 2) := fun k ↦
    PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k)
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ ι (u k)
  have hF₀Gradient (k : ℕ) : gradient F₀ (x k) = ι (g k) := by
    dsimp only [F₀, x, u]
    rw [hConj.gradientConjugate]
    apply hConj.gradientBijective.1
    rw [Function.rightInverse_invFun hConj.gradientBijective.2]
    exact (hH_gradient k).symm
  have hInfiniteNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hF₀Differentiable : Differentiable ℝ F₀ :=
    hF₀Smooth.differentiable hInfiniteNeZero
  let m : ℝ := 1 / (1 + θ)
  have hm : 0 < m := by
    dsimp only [m]
    positivity
  have hF₀Strong : StrongConvexOn Set.univ m F₀ := by
    simpa only [m, F₀] using hConj.strongConvex
  -- The planar recurrence supplies all secant and exact-line-search hypotheses.
  obtain ⟨B, α, hRun⟩ :=
    PlanarGradient.IsAlternatingScale.existsTrajectory_of_embeddedCandidates hAlt ι F₀ m
    hF₀Differentiable hm hF₀Strong hF₀Gradient
  have hσ_nonneg : 0 ≤ σ := hσ.1.le
  have huSuperlinear : QConvergence.IsSuperlinear u 0 := by
    exact PlanarGradient.IsAlternatingScale.candidateIsSuperlinear hAlt hσ_nonneg
  have huOrder : QConvergence.order u 0 = 1 := by
    exact PlanarGradient.IsAlternatingScale.candidateOrderEqOne hAlt hσ_nonneg
  have hxSuperlinear : QConvergence.IsSuperlinear x 0 := by
    have hEmbedded := QConvergence.isSuperlinear_linearIsometry ι u 0 huSuperlinear
    simpa only [x, map_zero] using hEmbedded
  have hxOrder : QConvergence.order x 0 = 1 := by
    have hEmbedded := QConvergence.order_linearIsometry ι u 0
    simpa only [x, map_zero, huOrder] using hEmbedded
  have hxNonzero (k : ℕ) : x k ≠ 0 := by
    intro hxZero
    have huZero : u k = 0 := by
      apply ι.injective
      simpa only [x, map_zero] using hxZero
    have hLower : ‖g k‖ ≤ ‖u k‖ := by
      dsimp only [u]
      exact (PlanarGradient.IsAlternatingScale.candidateNormBounds hAlt k).1
    have hgNormZero : ‖g k‖ = 0 := by
      apply le_antisymm
      · simpa only [huZero, norm_zero] using hLower
      · exact norm_nonneg (g k)
    exact hAlt.nonzero k (norm_eq_zero.mp hgNormZero)
  -- Choose one explicit dilation that dominates both the compact support and the
  -- initial candidate, making their scaled images lie strictly inside the radius `R`.
  let A : ℝ := 1 + 2 * ‖g 0‖
  have hA_pos : 0 < A := by
    dsimp only [A]
    positivity
  let cScale : ℝ := R / A
  have hcScale_pos : 0 < cScale := by
    dsimp only [cScale]
    exact div_pos hR hA_pos
  have hcScale_ne : cScale ≠ 0 := hcScale_pos.ne'
  have hcScaleA : cScale * A = R := by
    dsimp only [cScale]
    exact div_mul_cancel₀ R hA_pos.ne'
  have hTailRadiusNonneg : 0 ≤ 5 * ‖g 0‖ / 4 := by positivity
  have hTailRadiusLtA : 5 * ‖g 0‖ / 4 < A := by
    dsimp only [A]
    nlinarith [norm_nonneg (g 0)]
  have hScaledTailRadius : cScale * (5 * ‖g 0‖ / 4) < R := by
    calc
      cScale * (5 * ‖g 0‖ / 4) < cScale * A :=
        mul_lt_mul_of_pos_left hTailRadiusLtA hcScale_pos
      _ = R := hcScaleA
  have huZeroBound : ‖u 0‖ ≤ (1 + σ) * ‖g 0‖ := by
    dsimp only [u]
    exact (PlanarGradient.IsAlternatingScale.candidateNormBounds hAlt 0).2
  have hgZeroNormPos : 0 < ‖g 0‖ := norm_pos_iff.mpr (hAlt.nonzero 0)
  have hSigmaGap : 0 < (1 - σ) * ‖g 0‖ := by
    exact mul_pos (sub_pos.mpr hσ.2) hgZeroNormPos
  have huZeroLtA : ‖u 0‖ < A := by
    apply huZeroBound.trans_lt
    dsimp only [A]
    nlinarith
  have hScaledInitialRadius : cScale * ‖u 0‖ < R := by
    calc
      cScale * ‖u 0‖ < cScale * A :=
        mul_lt_mul_of_pos_left huZeroLtA hcScale_pos
      _ = R := hcScaleA
  let F : EuclideanSpace ℝ (Fin n) → ℝ := Scale.objective cScale F₀
  let xScaled : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ cScale • x k
  let x₀ : EuclideanSpace ℝ (Fin n) := cScale • x 0
  have hScaledSmooth : ContDiff ℝ ∞ F := by
    dsimp only [F]
    exact Scale.objective_contDiff cScale hF₀Smooth
  have hScaledTailFormula :
      F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) =
        (fun r : ℝ ↦ cScale ^ 2 * r) ∘
          (fun z ↦
            (F₀ - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
              (cScale⁻¹ • z)) := by
    funext z
    dsimp only [F]
    exact Scale.objective_sub_standardQuadratic_apply hcScale_ne F₀ z
  have hDilationSmooth : ContDiff ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) ↦ cScale⁻¹ • z) := by
    fun_prop
  have hComposedTailSmooth : ContDiff ℝ ∞
      (fun z ↦ (F₀ - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
        (cScale⁻¹ • z)) := hF₀TailSmooth.comp hDilationSmooth
  have hValueScaleSmooth : ContDiff ℝ ∞ (fun r : ℝ ↦ cScale ^ 2 * r) := by
    fun_prop
  have hScaledTailSmooth : ContDiff ℝ ∞
      (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
    rw [hScaledTailFormula]
    exact hValueScaleSmooth.comp hComposedTailSmooth
  have hcScaleInvNe : cScale⁻¹ ≠ 0 := inv_ne_zero hcScale_ne
  have hComposedTailCompact : HasCompactSupport
      (fun z ↦ (F₀ - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
        (cScale⁻¹ • z)) := hF₀TailCompact.comp_smul hcScaleInvNe
  have hValueScaleZero : (fun r : ℝ ↦ cScale ^ 2 * r) 0 = 0 := by
    exact mul_zero (cScale ^ 2)
  have hScaledTailCompact : HasCompactSupport
      (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
    rw [hScaledTailFormula]
    simpa only [Function.comp_apply] using
      hComposedTailCompact.comp_left hValueScaleZero
  have hScaledSupport :
      tsupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
        Metric.ball 0 R := by
    dsimp only [F]
    rw [Scale.tsupport_sub_quadratic hcScale_ne]
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.mp hz
    have hyBall := hF₀Support hy
    rw [Metric.mem_closedBall, dist_zero_right] at hyBall
    rw [← hyz, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hcScale_pos]
    exact (mul_le_mul_of_nonneg_left hyBall hcScale_pos.le).trans_lt hScaledTailRadius
  have hx₀Mem : x₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    dsimp only [x₀, x]
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hcScale_pos, ι.norm_map]
    exact hScaledInitialRadius
  have hLocalized :
      tsupport (F - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∪ {x₀} ⊆
        Metric.ball 0 R := by
    exact Set.union_subset hScaledSupport (Set.singleton_subset_iff.mpr hx₀Mem)
  have hScaledStrong : StrongConvexOn Set.univ m F := by
    dsimp only [F]
    exact Scale.strongConvexOn_objective hcScale_ne hF₀Strong
  have hScaledStrongExists : ∃ m' > 0, StrongConvexOn Set.univ m' F :=
    ⟨m, hm, hScaledStrong⟩
  have hTwoLeInfty : (2 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (OrderTop.le_top 2)
  have hF₀Two : ContDiff ℝ 2 F₀ := hF₀Smooth.of_le hTwoLeInfty
  have hScaledHessian (z : EuclideanSpace ℝ (Fin n)) :
      ConvexAnalysis.hessian F z = ConvexAnalysis.hessian F₀ (cScale⁻¹ • z) := by
    dsimp only [F]
    have hMatrix := Scale.hessian_objective hcScale_ne hF₀Two z
    have hDerivative :
        fderiv ℝ (gradient (Scale.objective cScale F₀)) z =
          fderiv ℝ (gradient F₀) (cScale⁻¹ • z) :=
      (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n))).symm.injective hMatrix
    have hLeft := ConvexAnalysis.toEuclideanCLM_hessian
      (Scale.objective cScale F₀) z
    have hRight := ConvexAnalysis.toEuclideanCLM_hessian F₀ (cScale⁻¹ • z)
    apply (Matrix.toEuclideanCLM :
      Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).injective
    exact hLeft.trans (hDerivative.trans hRight.symm)
  have hScaledHessianClose : ∃ η : ℝ, 0 ≤ η ∧ η < ε ∧
      ∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian F z - 1‖ ≤ η := by
    refine ⟨θ / (1 - θ), hη_nonneg, hη_lt, ?_⟩
    intro z
    rw [hScaledHessian z]
    exact hConj.hessianNorm (cScale⁻¹ • z)
  have hF₀Min : IsMinOn F₀ Set.univ 0 := by
    simpa only [F₀] using (hConj.uniqueMinimizer 0).2 rfl
  have hScaledMin : IsMinOn F Set.univ 0 := by
    rw [isMinOn_univ_iff] at hF₀Min ⊢
    intro z
    dsimp only [F]
    rw [Scale.objective_apply, Scale.objective_apply, smul_zero]
    exact mul_le_mul_of_nonneg_left (hF₀Min (cScale⁻¹ • z)) (sq_nonneg cScale)
  have hScaledUnique (z : EuclideanSpace ℝ (Fin n)) :
      IsMinOn F Set.univ z ↔ z = 0 := by
    constructor
    · intro hz
      exact (hScaledStrong.strictConvexOn hm).eq_of_isMinOn hz hScaledMin
        (Set.mem_univ z) (Set.mem_univ 0)
    · intro hz
      rw [hz]
      exact hScaledMin
  have hScaledHessianZero : ConvexAnalysis.hessian F 0 = 1 := by
    rw [hScaledHessian 0, smul_zero]
    simpa only [F₀] using hConj.hessianZero
  have hScaledRun :
      IsTrajectory F (1 : Matrix (Fin n) (Fin n) ℝ) xScaled B α := by
    simpa only [F, xScaled] using IsTrajectory.scale hRun hcScale_ne
  have hScaledNonzero (k : ℕ) : xScaled k ≠ 0 := by
    dsimp only [xScaled]
    exact smul_ne_zero hcScale_ne (hxNonzero k)
  have hScaledSuperlinear : QConvergence.IsSuperlinear xScaled 0 := by
    have hRate :=
      QConvergence.isSuperlinear_smul x 0 cScale hcScale_ne hxSuperlinear
    simpa only [xScaled, smul_zero] using hRate
  have hScaledOrder : QConvergence.order xScaled 0 = 1 := by
    have hRate := QConvergence.order_smul (x := x) (xStar := 0) hcScale_ne
    simpa only [xScaled, smul_zero, hxOrder] using hRate
  have hInitial : xScaled 0 = x₀ := rfl
  -- Every field now follows from a named objective, localization, run, or rate fact.
  refine ⟨F, x₀, xScaled, B, α, ?_⟩
  exact IsOrderOneExample.ofConditions hScaledSmooth hScaledStrongExists
    hScaledTailSmooth hScaledTailCompact hLocalized hScaledHessianClose
    hScaledUnique hScaledHessianZero hInitial hScaledRun hScaledNonzero
    hScaledSuperlinear hScaledOrder

namespace IsTrajectory

/-- Every nonterminating convergent exact-line-search BFGS trajectory for a smooth
globally strongly convex objective at a nondegenerate minimizer has Q-order at least
one. -/
theorem one_le_order {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (B₀ : Matrix (Fin n) (Fin n) ℝ) (B : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (α : ℕ → ℝ) (m : ℝ) (h_m : 0 < m)
    (h_smooth : ContDiff ℝ ⊤ F) (h_strongConvex : StrongConvexOn Set.univ m F)
    (h_min : IsMinOn F Set.univ xStar)
    (h_hessian : (ConvexAnalysis.hessian F xStar).PosDef)
    (h_run : BFGS.IsTrajectory F B₀ x B α) (h_ne : ∀ k, x k ≠ xStar)
    (h_tendsto : Filter.Tendsto x Filter.atTop (𝓝 xStar)) :
    (1 : ENNReal) ≤ QConvergence.order x xStar := by
  -- Fermat's theorem turns global minimality into the critical-point hypothesis.
  have h_gradient : gradient F xStar = 0 := by
    apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
    rw [toDual_gradient, map_zero]
    exact (h_min.isLocalMin (isOpen_univ.mem_nhds (Set.mem_univ xStar))).fderiv_eq_zero
  have h_hessian' : Matrix.PosDef
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (gradient F) xStar)) := by
    rw [← ConvexAnalysis.toEuclideanCLM_hessian F xStar]
    simpa only [StarAlgEquiv.symm_apply_apply] using h_hessian
  have h_recurrence : ∀ k, x (k + 1) =
      x k + α k • searchDirection (B k) (gradient F (x k)) :=
    (isTrajectory_iff F B₀ x B α).mp h_run |>.2.2.2.2.1
  -- Package every BFGS step as an exact line-search step for the analytic theorem.
  have h_step : ∀ k, ∃ (d : EuclideanSpace ℝ (Fin n)) (a : ℝ),
      LineSearch.IsExact F (x k) d a ∧ x (k + 1) = x k + a • d := by
    intro k
    exact ⟨searchDirection (B k) (gradient F (x k)), α k,
      h_run.exact k, h_recurrence k⟩
  have h_order : QConvergence.HasOrderAtLeast x xStar 1 := by
    have hTwoLeAnalytic : (2 : ℕ∞ω) ≤ ⊤ := by norm_num
    exact QConvergence.hasOrderAtLeast_one_of_exactLineSearch F xStar x
      (h_smooth.contDiffAt.of_le hTwoLeAnalytic) h_gradient h_hessian'
      h_tendsto (Filter.Eventually.of_forall h_ne) h_step
  -- Exponent one belongs to the set whose supremum defines Q-order.
  rw [QConvergence.order_def]
  apply le_sSup
  exact ⟨1, (QConvergence.mem_admissibleExponents x xStar 1).mpr h_order,
    ENNReal.ofReal_one⟩

end IsTrajectory

end BFGS
