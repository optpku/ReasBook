module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConvexFunction
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCases
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ImageReduction
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Optimality
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Trajectory
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.CertificateStorage
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.ReducedOrbitLimit
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.ReducedNormalization
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.ReducedTransport
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.ParameterCoverage
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace ADMM

namespace Trajectory

/-- The objective-value sequence along an exact ADMM trajectory. -/
noncomputable def objectiveValue {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) (k : ℕ) : EReal :=
  P.objective (t.x k) (t.y k)

/-- Evaluation of the objective-value sequence along an exact ADMM trajectory. -/
theorem objectiveValue_apply {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) (k : ℕ) :
    t.objectiveValue k = P.objective (t.x k) (t.y k) := by
  -- Unfolding the objective-value sequence exposes its value at the given iterate.
  rfl

end Trajectory

/-- The image reduction supplies the static problem data needed by
the convergence argument in `ADMM.leftImage_tendsto`; keeping this interface
named avoids unfolding the reduced problem in the main theorem. -/
private theorem reducedProblemData {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    IsClosedProperConvex (P.reduced β).f ∧
      IsClosedProperConvex (P.reduced β).g ∧
      (∃ q v u, (P.reduced β).IsKKT q v u) ∧
      (P.reduced β).optimalValue = P.optimalValue / (β : EReal) := by
  -- Collect convexity, KKT existence, and the optimal-value identity from the
  -- image-reduction API before any orbit argument is attempted.
  refine ⟨Problem.reducedFirst_isClosedProperConvex P hf hg hKKT hβ hγ z,
    Problem.reducedSecond_isClosedProperConvex P hf hg hKKT hβ hγ z,
    Problem.reduced_exists_kkt P hf hg hKKT hβ hγ z,
    Problem.reduced_optimalValue P hf hg hKKT hβ hγ z⟩

/-- The reduced trajectory satisfies the two proximal graph laws and the scaled
multiplier recurrence used by `ADMM.leftImage_tendsto`. -/
private theorem reducedTrajectoryLaws {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    ∀ k,
      IsProxPoint (P.reduced β).f
        (-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k)
        (P.A.mulVec (z.x (k + 1))) ∧
      IsProxPoint (P.reduced β).g
        (-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k)
        (P.B.mulVec (z.y (k + 1)) - P.b) ∧
      β⁻¹ • z.multiplier (k + 1) = β⁻¹ • z.multiplier k +
        γ • (P.A.mulVec (z.x (k + 1)) +
          (P.B.mulVec (z.y (k + 1)) - P.b)) := by
  -- The three conjuncts are exactly the two reduced proximal updates and the
  -- scaled multiplier update supplied by the trajectory bridge lemmas.
  intro k
  exact ⟨Trajectory.firstImage_isProxPoint P hf hg hKKT hβ hγ z k,
    Trajectory.secondImage_isProxPoint P hf hg hKKT hβ hγ z k,
    Trajectory.scaledMultiplier_imageUpdate P hf hg hKKT hβ hγ z k⟩

/-- The regularized objective at a proximal point has a finite real value;
the interface is used by `ADMM.leftImage_tendsto` to expose the finite terms
needed by a storage estimate. -/
private theorem proximalValue_isReal {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {z x : Fin n → ℝ} (hx : IsProxPoint φ z x) :
    ∃ r : ℝ,
      φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) = r := by
  -- The finite-value component is exactly the first projection of the
  -- proximal characterization.
  exact (isProxPoint_iff.mp hx).imp fun r h ↦ h.1

/-- Helper for ADMM.leftImage_tendsto: the objective itself has a finite real
value at every proximal point. -/
private theorem proximalObjective_isReal {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {z x : Fin n → ℝ} (hx : IsProxPoint φ z x) :
    ∃ r : ℝ, φ x = r := by
  -- First expose the finite regularized value supplied by proximality.
  obtain ⟨s, hs⟩ := proximalValue_isReal hx
  let q := dotProduct (x - z) (x - z) / 2
  -- Subtracting the finite quadratic term leaves a finite objective value.
  refine ⟨s - q, ?_⟩
  have hs' : φ x + (q : EReal) = (s : EReal) := by
    simpa only [q] using hs
  have hcancel := congrArg (fun a : EReal ↦ a - (q : EReal)) hs'
  simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub] using hcancel

/-- Convexity bounds an extended-real objective on a segment joining two
points where the objective is finite. -/
private lemma convexObjective_segmentBound {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    {x y : Fin n → ℝ} (hx_top : φ x ≠ ⊤) (hy_top : φ y ≠ ⊤)
    {t : ℝ} (ht_zero : 0 ≤ t) (ht_one : t ≤ 1) :
    φ ((1 - t) • x + t • y) ≤
      (((1 - t) * (φ x).toReal + t * (φ y).toReal : ℝ) : EReal) := by
  -- Realize both finite values as points of the closed convex epigraph.
  have hx : (x, (φ x).toReal) ∈
      {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, EReal.coe_toReal hx_top (hφ.ne_bot x), le_refl]
  have hy : (y, (φ y).toReal) ∈
      {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, EReal.coe_toReal hy_top (hφ.ne_bot y), le_refl]
  have hweights : 1 - t + t = 1 := by
    ring
  have hconvex := hφ.epigraph_convex hx hy (sub_nonneg.mpr ht_one) ht_zero hweights
  -- Project the epigraph segment inequality to its objective coordinate.
  simpa only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_mk,
    smul_eq_mul, one_mul, EReal.coe_toReal hx_top (hφ.ne_bot x),
    EReal.coe_toReal hy_top (hφ.ne_bot y)] using hconvex

/-- Proximal minimality for a closed proper convex objective yields the real
support inequality at every finite comparison point. -/
private lemma proximalPoint_supportingInequality {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    {center x y : Fin n → ℝ} (hx : IsProxPoint φ center x)
    (hy_top : φ y ≠ ⊤) :
    (φ x).toReal - (φ y).toReal ≤
      dotProduct (center - x) (x - y) := by
  obtain ⟨r, hxvalue, hxmin⟩ := isProxPoint_iff.mp hx
  obtain ⟨cx, hφx⟩ := proximalObjective_isReal hx
  have hx_top : φ x ≠ ⊤ := by
    rw [hφx]
    exact EReal.coe_ne_top cx
  -- Compare the minimizer with points that approach it along the segment to `y`.
  have hbound : ∀ k : ℕ,
      (φ x).toReal - (φ y).toReal ≤
        dotProduct (center - x) (x - y) +
          (1 / ((k : ℝ) + 1)) * (dotProduct (y - x) (y - x) / 2) := by
    intro k
    let t : ℝ := 1 / ((k : ℝ) + 1)
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have ht_one : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one]
      · norm_num
      · positivity
    let q : Fin n → ℝ := (1 - t) • x + t • y
    have hsegment : φ q ≤
        (((1 - t) * (φ x).toReal + t * (φ y).toReal : ℝ) : EReal) := by
      exact convexObjective_segmentBound hφ hx_top hy_top ht_pos.le ht_one
    have hereal := (hxmin q).trans (add_le_add_left hsegment _)
    have hreal :
        (φ x).toReal + dotProduct (x - center) (x - center) / 2 ≤
          ((1 - t) * (φ x).toReal + t * (φ y).toReal) +
            dotProduct (q - center) (q - center) / 2 := by
      have hereal' :
          ((φ x).toReal : EReal) +
              ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) ≤
            (((1 - t) * (φ x).toReal + t * (φ y).toReal : ℝ) : EReal) +
              ((dotProduct (q - center) (q - center) / 2 : ℝ) : EReal) := by
        calc
          ((φ x).toReal : EReal) +
                ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) =
              φ x + ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) := by
                rw [EReal.coe_toReal hx_top (hφ.ne_bot x)]
          _ ≤ _ := hereal
      apply EReal.coe_le_coe_iff.mp
      simpa only [← EReal.coe_add] using hereal'
    have hq_sub : q - center = (x - center) + t • (y - x) := by
      dsimp [q]
      module
    have hlinear :
        dotProduct (x - center) (y - x) =
          dotProduct (center - x) (x - y) := by
      simp only [sub_dotProduct, dotProduct_sub]
      ring
    have hquadratic :
        dotProduct (q - center) (q - center) / 2 =
          dotProduct (x - center) (x - center) / 2 +
            t * dotProduct (center - x) (x - y) +
              t ^ 2 * (dotProduct (y - x) (y - x) / 2) := by
      rw [hq_sub]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm (y - x) (x - center)]
      nlinarith [hlinear]
    rw [hquadratic] at hreal
    dsimp [t] at hreal ⊢
    nlinarith
  -- Let the quadratic segment remainder tend to zero.
  have htendsto : Filter.Tendsto
      (fun k : ℕ ↦ dotProduct (center - x) (x - y) +
        (1 / ((k : ℝ) + 1)) * (dotProduct (y - x) (y - x) / 2))
      Filter.atTop (nhds (dotProduct (center - x) (x - y))) := by
    have hconst : Filter.Tendsto
        (fun _ : ℕ ↦ dotProduct (center - x) (x - y)) Filter.atTop
        (nhds (dotProduct (center - x) (x - y))) := tendsto_const_nhds
    simpa only [zero_mul, add_zero] using
      hconst.add (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const
        (dotProduct (y - x) (y - x) / 2))
  exact ge_of_tendsto' htendsto hbound

/-- A proximal point of a closed proper convex objective has subgradient equal
to its center minus the proximal point. -/
private lemma isSubgradientAt_of_isProxPoint {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    {center x : Fin n → ℝ} (hx : IsProxPoint φ center x) :
    IsSubgradientAt φ (center - x) x := by
  obtain ⟨c, hφx⟩ := proximalObjective_isReal hx
  refine ⟨c, hφx, ?_⟩
  intro y
  by_cases hy_top : φ y = ⊤
  · rw [hy_top]
    exact le_top
  · have hsupport := proximalPoint_supportingInequality hφ hx hy_top
    have hx_toReal : (φ x).toReal = c := by
      rw [hφx]
      exact EReal.toReal_coe c
    have hy_value : φ y = ((φ y).toReal : EReal) := by
      exact (EReal.coe_toReal hy_top (hφ.ne_bot y)).symm
    have hreverse : x - y = -(y - x) := by
      ext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [hφx, hy_value, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [hx_toReal, hreverse, dotProduct_neg] at hsupport
    linarith

/-- Helper for ADMM.leftImage_tendsto: each reduced proximal update supplies
the supporting subgradient used by the finite-memory storage argument. -/
theorem reducedTrajectorySubgradientLaws {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    ∀ k,
      IsSubgradientAt (P.reduced β).f
        (-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k -
          P.A.mulVec (z.x (k + 1)))
        (P.A.mulVec (z.x (k + 1))) ∧
      IsSubgradientAt (P.reduced β).g
        (-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k -
          (P.B.mulVec (z.y (k + 1)) - P.b))
        (P.B.mulVec (z.y (k + 1)) - P.b) := by
  -- Convert the two reduced proximal graph laws into explicit supporting
  -- subgradients, keeping the centers in the normal form used by the storage
  -- inequalities.
  intro k
  have hdata := reducedProblemData P hf hg hKKT hβ hγ z
  have hlaws := reducedTrajectoryLaws P hf hg hKKT hβ hγ z
  exact ⟨
    isSubgradientAt_of_isProxPoint hdata.1 (hlaws k).1,
    isSubgradientAt_of_isProxPoint hdata.2.1 (hlaws k).2.1⟩

/-- A newest-first history records the negated second image and the multiplier
scaled by the relaxation parameter. -/
private noncomputable def reducedFiniteMemoryHistory {m ℓ : ℕ}
    (v u : ℕ → Fin m → ℝ) (γ : ℝ) (k : ℕ) :
    (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ :=
  fun i ↦
    let t := k + i.1.rev.val
    if i.2 = 0 then -v t else γ⁻¹ • u t

/-- The residual of a reduced newest-first history is the current feasibility
residual whenever the multiplier satisfies the reduced ADMM recurrence. -/
private theorem reducedFiniteMemoryHistory_residual {m ℓ : ℕ}
    (q v u : ℕ → Fin m → ℝ) {γ : ℝ} (hγ : γ ≠ 0)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1)))
    (k : ℕ) (j : Fin (ℓ + 1)) :
    ADMM.FiniteMemory.residual (reducedFiniteMemoryHistory v u γ k) j =
      q (k + j.rev.val + 1) + v (k + j.rev.val + 1) := by
  -- Reverse indexing makes the two stored multiplier coordinates consecutive.
  rw [ADMM.FiniteMemory.residual_apply]
  dsimp [reducedFiniteMemoryHistory]
  simp only [Nat.reduceSubDiff]
  have hsub : ℓ + 1 - j.val = (ℓ - j.val) + 1 := by omega
  rw [hsub]
  rw [← Nat.add_assoc]
  rw [hrec (k + (ℓ - j.val))]
  simp [smul_add, smul_smul, hγ]

/-- The first graph position of a reduced newest-first history is the current
first image. -/
private theorem reducedFiniteMemoryHistory_firstPosition {m ℓ : ℕ}
    (q v u : ℕ → Fin m → ℝ) {γ : ℝ} (hγ : γ ≠ 0)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1)))
    (k : ℕ) (j : Fin (ℓ + 1)) :
    ADMM.FiniteMemory.graphPosition .F (reducedFiniteMemoryHistory v u γ k) j =
      q (k + j.rev.val + 1) := by
  -- Substitute the residual formula into the defining position coordinate.
  rw [ADMM.FiniteMemory.graphPosition_apply,
    reducedFiniteMemoryHistory_residual q v u hγ hrec]
  simp [reducedFiniteMemoryHistory, Fin.rev_castSucc, Nat.add_assoc]

/-- The second graph position of a reduced newest-first history is the negated
current second image. -/
private theorem reducedFiniteMemoryHistory_secondPosition {m ℓ : ℕ}
    (v u : ℕ → Fin m → ℝ) (γ : ℝ) (k : ℕ) (j : Fin (ℓ + 1)) :
    ADMM.FiniteMemory.graphPosition .J (reducedFiniteMemoryHistory v u γ k) j =
      -v (k + j.rev.val + 1) := by
  -- The second block position is stored directly in the first state coordinate.
  simp [ADMM.FiniteMemory.graphPosition_apply, reducedFiniteMemoryHistory,
    Fin.rev_castSucc, Nat.add_assoc]

/-- The first graph normal of a reduced newest-first history is the first
proximal center minus its graph position. -/
private theorem reducedFiniteMemoryHistory_firstNormal {m ℓ : ℕ}
    (q v u : ℕ → Fin m → ℝ) {γ : ℝ} (hγ : γ ≠ 0)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1)))
    (k : ℕ) (j : Fin (ℓ + 1)) :
    ADMM.FiniteMemory.graphNormal γ .F (reducedFiniteMemoryHistory v u γ k) j =
      -v (k + j.rev.val) - u (k + j.rev.val) - q (k + j.rev.val + 1) := by
  -- Expand the stored predecessor state and the already normalized first position.
  rw [ADMM.FiniteMemory.graphNormal_apply,
    reducedFiniteMemoryHistory_firstPosition q v u hγ hrec]
  simp [reducedFiniteMemoryHistory, Fin.rev_succ, hγ, Nat.add_assoc]

/-- The second graph normal of a reduced newest-first history is the transformed
second proximal center minus its graph position. -/
private theorem reducedFiniteMemoryHistory_secondNormal {m ℓ : ℕ}
    (q v u : ℕ → Fin m → ℝ) {γ : ℝ} (hγ : γ ≠ 0)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1)))
    (k : ℕ) (j : Fin (ℓ + 1)) :
    ADMM.FiniteMemory.graphNormal γ .J (reducedFiniteMemoryHistory v u γ k) j =
      u (k + j.rev.val) +
        (q (k + j.rev.val + 1) + v (k + j.rev.val + 1)) := by
  -- Combine the predecessor multiplier with the normalized history residual.
  rw [ADMM.FiniteMemory.graphNormal_apply,
    reducedFiniteMemoryHistory_residual q v u hγ hrec]
  simp [reducedFiniteMemoryHistory, Fin.rev_succ, hγ, Nat.add_assoc]

/-- Helper for ADMM.leftImage_tendsto: the feasibility component of a reduced
KKT triple is the zero-sum image condition used by the recentered proximal
orbit. -/
private theorem reducedKKT_feasible_zero {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    {β : ℝ} {q v u : Fin m → ℝ}
    (h : (P.reduced β).IsKKT q v u) : q + v = 0 := by
  -- The reduced matrices are identities and its right-hand side is zero.
  simpa only [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
    Matrix.one_mulVec, add_sub_cancel_right] using h.feasible

/-- The image-reduced exact orbit converges in its first image, shifted second
image, and scaled multiplier coordinates, with the corresponding original
optimality conclusions. -/
private theorem reducedOrbitConverges {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    ∃ qBar vBar uBar,
      Filter.Tendsto (fun k ↦ P.A.mulVec (z.x k)) Filter.atTop (nhds qBar) ∧
      Filter.Tendsto (fun k ↦ P.B.mulVec (z.y k) - P.b) Filter.atTop (nhds vBar) ∧
      Filter.Tendsto
        (fun k ↦ P.A.mulVec (z.x k) + (P.B.mulVec (z.y k) - P.b))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k ↦ (P.B.mulVec (z.y k) - P.b) -
          (P.B.mulVec (z.y (k - 1)) - P.b)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k ↦ z.objectiveValue k / (β : EReal)) Filter.atTop
        (nhds (P.optimalValue / (β : EReal))) ∧
      P.IsOptimalMultiplier (β • uBar) ∧
      Filter.Tendsto (fun k ↦ β⁻¹ • z.multiplier k) Filter.atTop (nhds uBar) ∧
      ∀ hA : Function.Injective P.A.mulVec, Function.Injective P.B.mulVec →
      ∀ xBar yBar, P.A.mulVec xBar = qBar → P.B.mulVec yBar - P.b = vBar →
        P.IsKKT xBar yBar (β • uBar) := by
  -- Reduce the original problem without imposing ranks on either constraint map.
  have hdata := reducedProblemData P hf hg hKKT hβ hγ z
  have hlaws := reducedTrajectoryLaws P hf hg hKKT hβ hγ z
  have hsubgrad := reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z
  obtain ⟨qStar, vStar, uStar, hReducedKKT⟩ := hdata.2.2.1
  have hfeasible : qStar + vStar = 0 := reducedKKT_feasible_zero P hReducedKKT
  have hfStar : IsSubgradientAt (P.reduced β).f (-uStar) qStar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hReducedKKT.firstStationary
  have hgStar : IsSubgradientAt (P.reduced β).g (-uStar) vStar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hReducedKKT.secondStationary
  let qSeq : ℕ → Fin m → ℝ := fun k ↦ P.A.mulVec (z.x k)
  let vSeq : ℕ → Fin m → ℝ := fun k ↦ P.B.mulVec (z.y k) - P.b
  let uSeq : ℕ → Fin m → ℝ := fun k ↦ β⁻¹ • z.multiplier k
  have hrec : ∀ k, uSeq (k + 1) = uSeq k + γ • (qSeq (k + 1) + vSeq (k + 1)) :=
    fun k ↦ (hlaws k).2.2
  have hfirst : ∀ k, IsSubgradientAt (P.reduced β).f
      (-vSeq k - uSeq k - qSeq (k + 1)) (qSeq (k + 1)) :=
    fun k ↦ (hsubgrad k).1
  have hsecond : ∀ k, IsSubgradientAt (P.reduced β).g
      (-qSeq (k + 1) - uSeq k - vSeq (k + 1)) (vSeq (k + 1)) :=
    fun k ↦ (hsubgrad k).2
  -- The classical energy covers the open lower interval. Exact rational
  -- certificates cover the four adjoining closed upper intervals.
  have hparameter : γ < 3 / 2 ∨ ∃ ℓ, Nonempty (ADMM.FiniteMemory.Certificate ℓ γ) := by
    by_cases hsmall : γ < 3 / 2
    · exact Or.inl hsmall
    · exact Or.inr (ConvergenceProof.parameter_has_certificate (le_of_not_gt hsmall) hγ_bound)
  -- Both branches provide boundedness and square-summable residuals. A common
  -- compactness and summably perturbed energy argument gives whole-orbit limits.
  obtain ⟨qBar, vBar, uBar, hq, hv, hu⟩ := ConvergenceProof.reduced_orbit_converges
    hγ hdata.1 hdata.2.1 qSeq vSeq uSeq qStar vStar uStar hfeasible hfStar hgStar
    hrec hfirst hsecond hparameter
  obtain ⟨hlimitFeasible, hfbar, hgbar⟩ := ConvergenceProof.reduced_limit_stationary
    hdata.1 hdata.2.1 hγ.ne' hrec hfirst hsecond hq hv hu
  have hkkt : (P.reduced β).IsKKT qBar vBar uBar := by
    refine Problem.IsKKT.ofConditions ?_ ?_ ?_
    · simpa [Problem.reduced_A, Matrix.one_mulVec] using hfbar
    · simpa [Problem.reduced_B, Matrix.one_mulVec] using hgbar
    · simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
        Matrix.one_mulVec] using hlimitFeasible
  obtain ⟨hF, hG⟩ := ConvergenceProof.reduced_objectives_tendsto
    hdata.1 hdata.2.1 hfirst hsecond hq hv hu
  -- Support-plane transport identifies the original optimal multiplier even
  -- without primal representatives on the limiting image fibers.
  obtain ⟨hr, hd, hobjective, hopt, hcompatible⟩ :=
    ConvergenceProof.reducedOrbitConclusions_from_limits P hf hg hKKT hβ hγ z
      hq hv hu hkkt hF hG
  exact ⟨qBar, vBar, uBar, hq, hv, hr, hd, hobjective, hopt, hu, hcompatible⟩

/-- Convergence of the rank-free image variables, residuals, objective values,
and multipliers, together with the KKT identification of any compatible primal
limits. -/
private theorem rankFreeConvergenceBundle {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    ∃ qBar vBar multiplierBar,
      Filter.Tendsto (fun k ↦ P.A.mulVec (z.x k)) Filter.atTop (nhds qBar) ∧
      Filter.Tendsto (fun k ↦ P.B.mulVec (z.y k)) Filter.atTop (nhds vBar) ∧
      Filter.Tendsto z.primalResidual Filter.atTop (nhds 0) ∧
      Filter.Tendsto z.secondIncrement Filter.atTop (nhds 0) ∧
      Filter.Tendsto z.objectiveValue Filter.atTop (nhds P.optimalValue) ∧
      P.IsOptimalMultiplier multiplierBar ∧
      Filter.Tendsto z.multiplier Filter.atTop (nhds multiplierBar) ∧
      ∀ hA : Function.Injective P.A.mulVec, Function.Injective P.B.mulVec →
      ∀ xBar yBar, P.A.mulVec xBar = qBar → P.B.mulVec yBar = vBar →
        P.IsKKT xBar yBar multiplierBar := by
  -- Obtain the three reduced-coordinate limits and their source-level conclusions.
  obtain ⟨qBar, vBar, uBar, hq, hv, hr, hd, hobj, hopt, hu, hkkt⟩ :=
    reducedOrbitConverges P hf hg hKKT hβ hγ hγ_bound z
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hβ_ereal_ne_bot : (β : EReal) ≠ ⊥ := EReal.coe_ne_bot β
  have hβ_ereal_ne_top : (β : EReal) ≠ ⊤ := EReal.coe_ne_top β
  have hβ_ereal_ne_zero : (β : EReal) ≠ 0 := EReal.coe_ne_zero.mpr hβ_ne
  -- Undo the affine shift in the second image coordinate.
  have hb : Filter.Tendsto (fun _ : ℕ ↦ P.b) Filter.atTop (nhds P.b) :=
    tendsto_const_nhds
  have hright : Filter.Tendsto (fun k ↦ P.B.mulVec (z.y k)) Filter.atTop
      (nhds (vBar + P.b)) := by
    simpa only [sub_add_cancel] using hv.add hb
  -- The reduced feasibility residual is the original primal residual.
  have hresidual : Filter.Tendsto z.primalResidual Filter.atTop (nhds 0) := by
    apply hr.congr'
    exact Filter.Eventually.of_forall fun k ↦ by
      rw [z.primalResidual_apply, add_sub_assoc]
  -- Cancellation of the affine shift identifies reduced and original increments.
  have hincrement : Filter.Tendsto z.secondIncrement Filter.atTop (nhds 0) := by
    apply hd.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    rw [z.secondIncrement_apply k hk, Matrix.mulVec_sub, sub_sub_sub_cancel_right]
  -- Multiplication by the finite nonzero penalty recovers the original objective values.
  have hobjective : Filter.Tendsto z.objectiveValue Filter.atTop
      (nhds P.optimalValue) := by
    have hscaled := EReal.Tendsto.const_mul hobj
      (Or.inl hβ_ereal_ne_bot) (Or.inl hβ_ereal_ne_top)
    simpa only [EReal.mul_div_cancel hβ_ereal_ne_bot hβ_ereal_ne_top
      hβ_ereal_ne_zero] using hscaled
  -- Undo the positive penalty scaling in the multiplier coordinate.
  have hmultiplier : Filter.Tendsto z.multiplier Filter.atTop (nhds (β • uBar)) := by
    simpa only [smul_smul, mul_inv_cancel₀ hβ_ne, one_smul] using hu.const_smul β
  refine ⟨qBar, vBar + P.b, β • uBar, hq, hright, hresidual, hincrement,
    hobjective, hopt, hmultiplier, ?_⟩
  intro hA hB xBar yBar hxImage hyImage
  apply hkkt hA hB xBar yBar hxImage
  rw [hyImage]
  exact add_sub_cancel_right vBar P.b

/-- An injective matrix map reflects convergence of a sequence from convergence
of its image, and the image limit lies in the matrix range. -/
private theorem tendstoOfMulVecTendstoOfInjective {n m : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) (s : ℕ → Fin n → ℝ) (q : Fin m → ℝ)
    (hL : Function.Injective L.mulVec)
    (hlim : Filter.Tendsto (fun k ↦ L.mulVec (s k)) Filter.atTop (nhds q)) :
    ∃ x, L.mulVec x = q ∧ Filter.Tendsto s Filter.atTop (nhds x) := by
  -- Regard matrix multiplication as a finite-dimensional linear closed embedding.
  have hker : LinearMap.ker L.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    simpa only [Matrix.coe_mulVecLin] using hL
  have hclosed : Topology.IsClosedEmbedding L.mulVecLin :=
    LinearMap.isClosedEmbedding_of_injective hker
  -- Closedness of the range supplies a preimage of the proposed image limit.
  have hq : q ∈ Set.range L.mulVecLin := by
    refine hclosed.isClosed_range.mem_of_tendsto hlim ?_
    exact Filter.Eventually.of_forall fun k ↦ ⟨s k, rfl⟩
  obtain ⟨x, hx⟩ := hq
  refine ⟨x, hx, ?_⟩
  -- The inducing part of the closed embedding reflects convergence to that preimage.
  apply (hclosed.tendsto_nhds_iff).2
  simpa [Function.comp_def, hx] using hlim

/-- The first constraint images of an exact ADMM trajectory converge. -/
theorem leftImage_tendsto {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    ∃ q : Fin m → ℝ,
      Filter.Tendsto (fun k ↦ P.A.mulVec (z.x k)) Filter.atTop (nhds q) := by
  -- Project the first image limit from the common rank-free convergence bundle.
  obtain ⟨qBar, vBar, multiplierBar, hq, hv, hr, hd, hobj, hopt, hmult, hkkt⟩ :=
    rankFreeConvergenceBundle P hf hg hKKT hβ hγ hγ_bound z
  exact ⟨qBar, hq⟩

/-- The second constraint images of an exact ADMM trajectory converge. -/
theorem rightImage_tendsto {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    ∃ q : Fin m → ℝ,
      Filter.Tendsto (fun k ↦ P.B.mulVec (z.y k)) Filter.atTop (nhds q) := by
  -- Project the second image limit from the common rank-free convergence bundle.
  obtain ⟨qBar, vBar, multiplierBar, hq, hv, hr, hd, hobj, hopt, hmult, hkkt⟩ :=
    rankFreeConvergenceBundle P hf hg hKKT hβ hγ hγ_bound z
  exact ⟨vBar, hv⟩

/-- The primal residuals of an exact ADMM trajectory tend to zero. -/
theorem primalResidual_tendsto_zero {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    Filter.Tendsto z.primalResidual Filter.atTop (nhds 0) := by
  -- Project residual convergence from the common rank-free convergence bundle.
  obtain ⟨qBar, vBar, multiplierBar, hq, hv, hr, hd, hobj, hopt, hmult, hkkt⟩ :=
    rankFreeConvergenceBundle P hf hg hKKT hβ hγ hγ_bound z
  exact hr

/-- The second-block image increments of an exact ADMM trajectory tend to zero. -/
theorem secondIncrement_tendsto_zero {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    Filter.Tendsto z.secondIncrement Filter.atTop (nhds 0) := by
  -- Project second-image asymptotic regularity from the common convergence bundle.
  obtain ⟨qBar, vBar, multiplierBar, hq, hv, hr, hd, hobj, hopt, hmult, hkkt⟩ :=
    rankFreeConvergenceBundle P hf hg hKKT hβ hγ hγ_bound z
  exact hd

/-- Objective values along an exact ADMM trajectory tend to the constrained optimum. -/
theorem objective_tendsto {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    Filter.Tendsto z.objectiveValue Filter.atTop (nhds P.optimalValue) := by
  -- Project objective-value convergence from the common rank-free convergence bundle.
  obtain ⟨qBar, vBar, multiplierBar, hq, hv, hr, hd, hobj, hopt, hmult, hkkt⟩ :=
    rankFreeConvergenceBundle P hf hg hKKT hβ hγ hγ_bound z
  exact hobj

/-- Multipliers along an exact ADMM trajectory converge to an optimal multiplier. -/
theorem multiplier_tendsto_optimal {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) :
    ∃ multiplier, P.IsOptimalMultiplier multiplier ∧
      Filter.Tendsto z.multiplier Filter.atTop (nhds multiplier) := by
  -- Project the optimal multiplier and its convergence from the common bundle.
  obtain ⟨qBar, vBar, multiplierBar, hq, hv, hr, hd, hobj, hopt, hmult, hkkt⟩ :=
    rankFreeConvergenceBundle P hf hg hKKT hβ hγ hγ_bound z
  exact ⟨multiplierBar, hopt, hmult⟩

/-- Injective constraint maps force an exact ADMM trajectory to converge to a KKT triple. -/
theorem trajectory_tendsto_kkt_of_injective {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_bound : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) (hA : Function.Injective P.A.mulVec)
    (hB : Function.Injective P.B.mulVec) :
    ∃ xBar yBar multiplierBar, P.IsKKT xBar yBar multiplierBar ∧
      Filter.Tendsto (fun k ↦ (z.x k, z.y k, z.multiplier k)) Filter.atTop
        (nhds (xBar, yBar, multiplierBar)) := by
  -- First obtain the rank-free limits and their compatibility with primal preimages.
  obtain ⟨qBar, vBar, multiplierBar, hq, hv, hr, hd, hobj, hopt, hmult, hkkt⟩ :=
    rankFreeConvergenceBundle P hf hg hKKT hβ hγ hγ_bound z
  -- Injectivity makes the two image convergences reflect to primal convergence.
  obtain ⟨xBar, hxImage, hx⟩ :=
    tendstoOfMulVecTendstoOfInjective P.A z.x qBar hA hq
  obtain ⟨yBar, hyImage, hy⟩ :=
    tendstoOfMulVecTendstoOfInjective P.B z.y vBar hB hv
  refine ⟨xBar, yBar, multiplierBar, hkkt hA hB xBar yBar hxImage hyImage, ?_⟩
  -- Assemble the three component limits in the nested product topology.
  exact hx.prodMk_nhds (hy.prodMk_nhds hmult)

end ADMM
