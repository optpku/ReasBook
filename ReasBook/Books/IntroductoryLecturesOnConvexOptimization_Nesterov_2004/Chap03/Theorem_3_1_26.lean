/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient EuclideanOrthant

universe u

variable {E : Type u}
variable {m : ℕ}

/- Theorem 3.1.26 lies in the convex inequality-constrained first-order optimality domain.

Sampled owner-style declarations:
- `LagrangianProblem.feasibleSet` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, the project owner for finite families of `≤ 0` constraints on a
  feasible subtype;
- `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible` and
  `LagrangianProblem.slaterCondition_iff` in `Chap01/Definition_1_10_9`, the canonical owner and
  bridge for strict feasibility;
- `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the owner for nonnegative
  multiplier vectors in `ℝ^m`;
- `gradient` / `∇` and `DifferentiableAt.hasGradientAt` in `Chap01/Definition_1_4_7`, the
  canonical owner and bridge for gradients of differentiable real-valued functions on a real
  inner-product space;
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Chap02/Theorem_2_29`, the
  chapter owner for constrained first-order optimality from explicit `HasGradientAt` data on a
  convex set.

Best owner abstraction:
- source-facing: the KKT optimality theorem below, because the textbook item is stated on an
  ambient set `Q ⊆ E` rather than on a pre-packaged problem structure;
- core/canonical: `LagrangianProblem`,
  `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible`,
  `nonnegativeOrthant m`, `gradient`, `DifferentiableAt`, `HasGradientAt`, and
  `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt`;
- bridge/view: the ambient feasible-set predicate `inequalityConstrainedFeasibleSet`.

Primitive data:
- the ambient feasible set `Q`;
- the objective `f0`;
- the finite inequality family `fi`;
- the candidate point `xStar`;
- the multiplier vector `lam : Λ`;
- the strict-feasibility certificate `∃ x ∈ Q, ∀ i : Fin m, fi i x < 0`;
- differentiability of `f0` and the constraint family `fi` on `Q`.

Derived API:
- `inequalityConstrainedFeasibleSet`;
- `mem_inequalityConstrainedFeasibleSet_iff`;
- the KKT optimality equivalence.

The earlier version fixed the ambient space to `EuclideanSpace ℝ (Fin n)` even though the public
surface only uses real inner-product-space structure. The refined file keeps the source-facing KKT
surface, reuses the Chapter 1 orthant owner for multiplier nonnegativity, and lowers the ambient
space to the weakest canonical layer used by the statements. The theorem now takes the
source-faithful strict-feasibility hypothesis directly instead of exporting a parallel set-based
Slater wrapper, and the main theorem exposes the KKT certificate directly through the canonical
gradients `∇ f0 xStar` and `∇ (fi i) xStar` instead of a one-off certificate wrapper. -/

/-- The feasible set of the inequality-constrained problem on the ambient set `Q` consists of the
points of `Q` satisfying every scalar constraint `fᵢ(x) ≤ 0`. -/
def inequalityConstrainedFeasibleSet
    (Q : Set E) (fi : Fin m → E → ℝ) : Set E :=
  {x | x ∈ Q ∧ ∀ i : Fin m, fi i x ≤ 0}

/-- Membership in `inequalityConstrainedFeasibleSet Q fi` means belonging to `Q` and satisfying
all scalar inequality constraints. -/
-- Proof sketch: unfold `inequalityConstrainedFeasibleSet`; membership in the set-builder is
-- definitionally the conjunction of `x ∈ Q` and `fi i x ≤ 0` for every constraint index `i`.
theorem mem_inequalityConstrainedFeasibleSet_iff
    {Q : Set E} {fi : Fin m → E → ℝ} {x : E} :
    x ∈ inequalityConstrainedFeasibleSet Q fi ↔
      x ∈ Q ∧ ∀ i : Fin m, fi i x ≤ 0 :=
  Iff.rfl

section

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "V" => Λ × ℝ

/-- Helper for Theorem 3.1.26: the value region records the constraint and objective slack data
achievable by points of `Q`. -/
def kktValueRegion
    (Q : Set E) (f0 : E → ℝ) (fi : Fin m → E → ℝ) (xStar : E) : Set V :=
  {p | ∃ x ∈ Q, (∀ i : Fin m, fi i x ≤ p.1 i) ∧ f0 x - f0 xStar ≤ p.2}

/-- Helper for Theorem 3.1.26: the strict negative orthant in `Λ × ℝ` is the region excluded by
primal optimality. -/
def kktNegativeRegion : Set V :=
  {p | (∀ i : Fin m, p.1 i < 0) ∧ p.2 < 0}

/-- Helper for Theorem 3.1.26: the weighted Lagrangian attached to a multiplier vector. -/
def weightedLagrangian
    (f0 : E → ℝ) (fi : Fin m → E → ℝ) (lam : Λ) : E → ℝ :=
  fun x ↦ f0 x + ∑ i : Fin m, lam i * fi i x

/-- Helper for Theorem 3.1.26: convexity of the objective and constraint family makes the value
region convex. -/
-- Proof sketch: interpolate two witnessing points in `Q`, then use the convexity inequalities
-- for `f0` and each `fi i` to bound the interpolated slack data.
theorem kkt_value_region_convex
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i)) :
    Convex ℝ (kktValueRegion Q f0 fi xStar) := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨x, hxQ, hxFi, hx0⟩
  rcases hq with ⟨y, hyQ, hyFi, hy0⟩
  refine ⟨a • x + b • y, hf0_conv.1 hxQ hyQ ha hb hab, ?_, ?_⟩
  · -- Each constraint value at the interpolated point stays below the interpolated slack level.
    intro i
    calc
      fi i (a • x + b • y) ≤ a * fi i x + b * fi i y := by
        simpa [smul_eq_mul] using (hfi_conv i).2 hxQ hyQ ha hb hab
      _ ≤ a * p.1 i + b * q.1 i := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hxFi i) ha)
          (mul_le_mul_of_nonneg_left (hyFi i) hb)
      _ = (a • p + b • q).1 i := by
        simp [smul_eq_mul]
  · -- The objective slack obeys the same convex interpolation bound.
    have hconv0 :
        f0 (a • x + b • y) - f0 xStar ≤
          a * (f0 x - f0 xStar) + b * (f0 y - f0 xStar) := by
      have hbase : f0 (a • x + b • y) ≤ a * f0 x + b * f0 y := by
        simpa [smul_eq_mul] using hf0_conv.2 hxQ hyQ ha hb hab
      calc
        f0 (a • x + b • y) - f0 xStar ≤ (a * f0 x + b * f0 y) - f0 xStar := by
          exact sub_le_sub_right hbase _
        _ = a * (f0 x - f0 xStar) + b * (f0 y - f0 xStar) := by
          calc
            a * f0 x + b * f0 y - f0 xStar
                = a * f0 x + b * f0 y - (a + b) * f0 xStar := by rw [hab, one_mul]
            _ = a * (f0 x - f0 xStar) + b * (f0 y - f0 xStar) := by ring
    calc
      f0 (a • x + b • y) - f0 xStar
          ≤ a * (f0 x - f0 xStar) + b * (f0 y - f0 xStar) := hconv0
      _ ≤ a * p.2 + b * q.2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hx0 ha)
          (mul_le_mul_of_nonneg_left hy0 hb)
      _ = (a • p + b • q).2 := by
        simp [smul_eq_mul]

/-- Helper for Theorem 3.1.26: a primal minimizer excludes strictly negative slack vectors from
the value region. -/
-- Proof sketch: a point in the intersection would yield a feasible `x ∈ Q` with all constraints
-- strict and objective value strictly below `f0 xStar`, contradicting `IsMinOn`.
theorem kkt_negative_region_disjoint
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hopt : IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar) :
    Disjoint kktNegativeRegion (kktValueRegion Q f0 fi xStar) := by
  refine Set.disjoint_left.2 ?_
  intro p hpNeg hpVal
  rcases hpVal with ⟨x, hxQ, hxFi, hx0⟩
  have hxFeas : x ∈ inequalityConstrainedFeasibleSet Q fi := by
    refine mem_inequalityConstrainedFeasibleSet_iff.2 ⟨hxQ, ?_⟩
    intro i
    exact (hxFi i).trans (hpNeg.1 i).le
  have hxMin : f0 xStar ≤ f0 x := (isMinOn_iff.mp hopt) x hxFeas
  have hxLt : f0 x < f0 xStar := by
    linarith [hx0, hpNeg.2]
  linarith

/-- Helper for Theorem 3.1.26: primal feasibility places the origin in the value region. -/
-- Proof sketch: use `xStar` itself as the witness; feasibility gives `fi i xStar ≤ 0` and the
-- objective slack at `xStar` is exactly zero.
theorem zero_mem_kktValueRegion_of_feasible
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi) :
    ((0 : Λ), (0 : ℝ)) ∈ kktValueRegion Q f0 fi xStar := by
  refine ⟨xStar, hxStar.1, ?_, by simp⟩
  intro i
  exact hxStar.2 i

/-- Helper for Theorem 3.1.26: the `i`-th standard basis vector in the Euclidean multiplier
space `Λ`. -/
def kktBasis (i : Fin m) : Λ :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (Pi.single i 1)

/-- Helper for Theorem 3.1.26: a continuous linear functional on `Λ × ℝ` is determined by its
values on the standard coordinate rays and the scalar axis. -/
-- Proof sketch: expand the `Λ`-coordinate in the standard basis `Pi.single i 1`, then use
-- linearity on the resulting decomposition of `(p, r)`.
theorem strongDual_apply_kkt_product
    (g : StrongDual ℝ V) (p : Λ) (r : ℝ) :
    g (p, r) = (∑ i : Fin m, p i * g (kktBasis i, (0 : ℝ))) +
      r * g ((0 : Λ), (1 : ℝ)) := by
  let e : Λ ≃ (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ
  have hp :
      p = ∑ i : Fin m, p i • kktBasis i := by
    apply e.injective
    ext j
    simp [e, kktBasis, Pi.single_apply]
  have hpair :
      (p, r) =
        (∑ i : Fin m, p i • ((kktBasis i, (0 : ℝ)) : V)) +
          r • (((0 : Λ), (1 : ℝ)) : V) := by
    refine Prod.ext ?_ ?_
    · have hfirst :
          ((∑ i : Fin m, p i • ((kktBasis i, (0 : ℝ)) : V)) +
              r • (((0 : Λ), (1 : ℝ)) : V)).1 = p := by
        calc
          ((∑ i : Fin m, p i • ((kktBasis i, (0 : ℝ)) : V)) +
              r • (((0 : Λ), (1 : ℝ)) : V)).1
              = ∑ i : Fin m, p i • kktBasis i := by
                  simp [Prod.fst_sum]
          _ = p := hp.symm
      simpa using hfirst.symm
    · have hsecond :
          ((∑ i : Fin m, p i • ((kktBasis i, (0 : ℝ)) : V)) +
              r • (((0 : Λ), (1 : ℝ)) : V)).2 = r := by
        simp [Prod.snd_sum]
      simpa using hsecond.symm
  calc
    g (p, r)
        = g
            ((∑ i : Fin m, p i • ((kktBasis i, (0 : ℝ)) : V)) +
              r • (((0 : Λ), (1 : ℝ)) : V)) := by
          rw [hpair]
    _ = g (∑ i : Fin m, p i • ((kktBasis i, (0 : ℝ)) : V)) +
          g (r • (((0 : Λ), (1 : ℝ)) : V)) := by
          rw [map_add]
    _ = (∑ i : Fin m, g (p i • ((kktBasis i, (0 : ℝ)) : V))) +
          g (r • (((0 : Λ), (1 : ℝ)) : V)) := by
          rw [map_sum]
    _ = (∑ i : Fin m, p i * g (kktBasis i, (0 : ℝ))) +
          r * g ((0 : Λ), (1 : ℝ)) := by
          rw [map_smul]
          refine congrArg (fun t : ℝ ↦ t + r * g ((0 : Λ), (1 : ℝ))) ?_
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [map_smul]
          simp [smul_eq_mul]

/-- Helper for Theorem 3.1.26: a Slater point gives a nonempty interior point of the KKT value
region. -/
-- Proof sketch: center an open upper box at the exact slack vector of the Slater point and keep
-- the same witness `xSlater` for every point in that box.
theorem kktValueRegion_interior_nonempty_of_slater
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    (interior (kktValueRegion Q f0 fi xStar)).Nonempty := by
  rcases hSlater with ⟨xSlater, hxSlaterQ, hxSlater⟩
  let e : Λ ≃ₜ (Fin m → ℝ) := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  let p0 : V := (e.symm (fun i ↦ fi i xSlater + 1), f0 xSlater - f0 xStar + 1)
  let WΛ : Set Λ := e ⁻¹' Set.pi Set.univ (fun i : Fin m ↦ Set.Ioi (fi i xSlater))
  let W : Set V := WΛ ×ˢ Set.Ioi (f0 xSlater - f0 xStar)
  have hp0_mem : p0 ∈ W := by
    constructor
    · change e p0.1 ∈ Set.pi Set.univ (fun i : Fin m ↦ Set.Ioi (fi i xSlater))
      simp [p0, e]
    · simp [W, p0]
  have hW_open : IsOpen W := by
    have hWΛ_open : IsOpen WΛ := by
      -- Rewrite the Euclidean coordinate condition through the canonical homeomorphism.
      dsimp [WΛ]
      exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).preimage e.continuous
    exact hWΛ_open.prod isOpen_Ioi
  have hW_subset : W ⊆ kktValueRegion Q f0 fi xStar := by
    intro p hp
    refine ⟨xSlater, hxSlaterQ, ?_, ?_⟩
    · intro i
      have hcoord :
          e p.1 i ∈ Set.Ioi (fi i xSlater) := (Set.mem_pi.mp hp.1) i (by simp)
      exact hcoord.le
    · exact hp.2.le
  refine ⟨p0, mem_interior_iff_mem_nhds.2 ?_⟩
  exact Filter.mem_of_superset (hW_open.mem_nhds hp0_mem) hW_subset

/-- Helper for Theorem 3.1.26: the origin is a boundary point of the KKT value region of a
primal minimizer. -/
-- Proof sketch: every neighborhood of the origin contains points on the negative diagonal
-- `((fun _ ↦ t), t)` with `t < 0`, but primal optimality forbids those points from entering the
-- value region.
theorem zero_not_mem_interior_kktValueRegion
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hopt : IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar) :
    ((0 : Λ), (0 : ℝ)) ∉ interior (kktValueRegion Q f0 fi xStar) := by
  intro hzero_int
  let e : Λ ≃ₜ (Fin m → ℝ) := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  let γ : ℝ → V := fun t ↦ (e.symm (fun _ : Fin m ↦ t), t)
  have hγ_cont : Continuous γ := by
    -- The diagonal curve is continuous after transporting along the Euclidean coordinate
    -- homeomorphism.
    have hsymm_cont : Continuous e.symm := e.symm.continuous
    exact (hsymm_cont.comp (continuous_pi fun _ ↦ continuous_id)).prodMk continuous_id
  have hpre_open :
      IsOpen (γ ⁻¹' interior (kktValueRegion Q f0 fi xStar)) :=
    isOpen_interior.preimage hγ_cont
  have hzero_pre : (0 : ℝ) ∈ γ ⁻¹' interior (kktValueRegion Q f0 fi xStar) := by
    simpa [γ] using hzero_int
  rcases Metric.mem_nhds_iff.mp (hpre_open.mem_nhds hzero_pre) with ⟨ε, hε_pos, hε_ball⟩
  have hhalf_mem :
      γ (-ε / 2) ∈ interior (kktValueRegion Q f0 fi xStar) := by
    apply hε_ball
    have hdist :
        dist (-ε / 2) (0 : ℝ) = ε / 2 := by
      rw [Real.dist_eq]
      have hneg : (-ε / 2 : ℝ) < 0 := by linarith
      rw [sub_zero, abs_of_neg hneg]
      ring
    simpa [hdist] using (half_lt_self hε_pos)
  have hhalf_neg : γ (-ε / 2) ∈ kktNegativeRegion := by
    constructor
    · intro i
      have hneg : (-ε / 2 : ℝ) < 0 := by linarith
      simpa [γ, e] using hneg
    · have hneg : (-ε / 2 : ℝ) < 0 := by linarith
      simpa [γ] using hneg
  have hhalf_val :
      γ (-ε / 2) ∈ kktValueRegion Q f0 fi xStar :=
    interior_subset hhalf_mem
  have hinter_eq_empty :
      kktNegativeRegion ∩ kktValueRegion Q f0 fi xStar = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp (kkt_negative_region_disjoint hopt)
  have hmem_inter :
      γ (-ε / 2) ∈ kktNegativeRegion ∩ kktValueRegion Q f0 fi xStar :=
    ⟨hhalf_neg, hhalf_val⟩
  have hempty_mem : γ (-ε / 2) ∈ (∅ : Set V) := by
    simpa [hinter_eq_empty] using hmem_inter
  exact hempty_mem.elim

/-- Helper for Theorem 3.1.26: support on the value region forces every coordinate-ray
coefficient of the separator to be nonnegative. -/
-- Proof sketch: realize each coordinate ray with the feasible point `xStar`, then read off the
-- separator inequality on that point of the value region.
theorem kkt_supporting_coordinate_nonnegative
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    {g : StrongDual ℝ V}
    (hsupport : ∀ p ∈ kktValueRegion Q f0 fi xStar, 0 ≤ g p)
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi) :
    ∀ i : Fin m, 0 ≤ g (kktBasis i, (0 : ℝ)) := by
  intro i
  have hmem :
      (kktBasis i, (0 : ℝ)) ∈ kktValueRegion Q f0 fi xStar := by
    refine ⟨xStar, hxStar.1, ?_, by simp⟩
    intro j
    have hnonneg : 0 ≤ (kktBasis i) j := by
      by_cases hji : j = i
      · simp [kktBasis, hji]
      · simp [kktBasis, hji]
    exact (hxStar.2 j).trans hnonneg
  simpa using hsupport _ hmem

/-- Helper for Theorem 3.1.26: support on the value region makes the scalar-axis coefficient of
the separator nonnegative. -/
-- Proof sketch: test the separator on the scalar-axis point realized again by the feasible point
-- `xStar`.
theorem kkt_supporting_scalar_nonnegative
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    {g : StrongDual ℝ V}
    (hsupport : ∀ p ∈ kktValueRegion Q f0 fi xStar, 0 ≤ g p)
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi) :
    0 ≤ g ((0 : Λ), (1 : ℝ)) := by
  have hmem : ((0 : Λ), (1 : ℝ)) ∈ kktValueRegion Q f0 fi xStar := by
    refine ⟨xStar, hxStar.1, ?_, by linarith⟩
    intro i
    exact hxStar.2 i
  simpa using hsupport _ hmem

/-- Helper for Theorem 3.1.26: the scalar-axis coefficient of a nonzero separator cannot vanish
under the Slater condition. -/
-- Proof sketch: if the scalar coefficient were zero, the Slater point would force every
-- coordinate coefficient to vanish; the product expansion would then show `g = 0`.
theorem kkt_supporting_scalar_ne_zero_of_slater
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    {g : StrongDual ℝ V} (hg_ne : g ≠ 0)
    (hsupport : ∀ p ∈ kktValueRegion Q f0 fi xStar, 0 ≤ g p)
    (hcoord_nonneg : ∀ i : Fin m, 0 ≤ g (kktBasis i, (0 : ℝ)))
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    g ((0 : Λ), (1 : ℝ)) ≠ 0 := by
  intro hμ_zero
  rcases hSlater with ⟨xSlater, hxSlaterQ, hxSlater⟩
  let coeff : Fin m → ℝ := fun i ↦ g (kktBasis i, (0 : ℝ))
  have hslater_support :
      0 ≤ ∑ i : Fin m, fi i xSlater * coeff i := by
    have hmem :
        (((EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦ fi i xSlater), f0 xSlater - f0 xStar) ∈
          kktValueRegion Q f0 fi xStar := by
      exact ⟨xSlater, hxSlaterQ, fun i ↦ le_rfl, le_rfl⟩
    have hsupp := hsupport _ hmem
    rw [strongDual_apply_kkt_product] at hsupp
    simpa [coeff, hμ_zero] using hsupp
  have hslater_sum_nonpos :
      ∑ i : Fin m, fi i xSlater * coeff i ≤ 0 := by
    refine Finset.sum_nonpos fun i _ ↦ ?_
    exact mul_nonpos_of_nonpos_of_nonneg (hxSlater i).le (hcoord_nonneg i)
  have hslater_sum_eq_zero :
      ∑ i : Fin m, fi i xSlater * coeff i = 0 :=
    le_antisymm hslater_sum_nonpos hslater_support
  have hneg_sum_eq_zero :
      ∑ i : Fin m, (-fi i xSlater) * coeff i = 0 := by
    calc
      ∑ i : Fin m, (-fi i xSlater) * coeff i
          = -∑ i : Fin m, fi i xSlater * coeff i := by
            simp [Finset.sum_neg_distrib, coeff, mul_comm, mul_left_comm, mul_assoc]
      _ = 0 := by simp [hslater_sum_eq_zero]
  have hcoeff_zero : ∀ i : Fin m, coeff i = 0 := by
    intro i
    have hterm_nonneg :
        ∀ j ∈ (Finset.univ : Finset (Fin m)), 0 ≤ (-fi j xSlater) * coeff j := by
      intro j hj
      exact mul_nonneg (by linarith [hxSlater j]) (hcoord_nonneg j)
    have hterm_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hneg_sum_eq_zero i (by simp)
    have hleft_ne : -fi i xSlater ≠ 0 := by
      linarith [hxSlater i]
    exact (mul_eq_zero.mp hterm_zero).resolve_left hleft_ne
  have hg_zero : g = 0 := by
    apply ContinuousLinearMap.ext
    intro p
    rcases p with ⟨p, r⟩
    rw [strongDual_apply_kkt_product]
    simp [coeff, hcoeff_zero, hμ_zero]

  exact hg_ne hg_zero

/-- Helper for Theorem 3.1.26: a supporting functional at the boundary point `0` has
nonnegative coordinate coefficients, and its scalar coefficient is strictly positive. -/
-- Proof sketch: combine the coordinate-ray and scalar-axis support lemmas, then use the Slater
-- point to upgrade the scalar-axis coefficient from nonnegative to strictly positive.
theorem kkt_supporting_coefficients_nonnegative_and_scalar_pos
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    {g : StrongDual ℝ V} (hg_ne : g ≠ 0)
    (hsupport : ∀ p ∈ kktValueRegion Q f0 fi xStar, 0 ≤ g p)
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi)
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    (∀ i : Fin m, 0 ≤ g (kktBasis i, (0 : ℝ))) ∧ 0 < g ((0 : Λ), (1 : ℝ)) := by
  have hcoord_nonneg :
      ∀ i : Fin m, 0 ≤ g (kktBasis i, (0 : ℝ)) :=
    kkt_supporting_coordinate_nonnegative hsupport hxStar
  have hμ_nonneg : 0 ≤ g ((0 : Λ), (1 : ℝ)) :=
    kkt_supporting_scalar_nonnegative hsupport hxStar
  have hμ_ne : g ((0 : Λ), (1 : ℝ)) ≠ 0 :=
    kkt_supporting_scalar_ne_zero_of_slater hg_ne hsupport hcoord_nonneg hSlater
  exact ⟨hcoord_nonneg, lt_of_le_of_ne hμ_nonneg hμ_ne.symm⟩

/-- Helper for Theorem 3.1.26: normalizing a supporting functional with positive scalar
coefficient yields the scalar weighted-value inequality. -/
-- Proof sketch: evaluate the support inequality on the exact slack point of `x`, expand the
-- functional in coordinates, and divide by the positive scalar coefficient.
theorem weighted_value_inequality_of_supporting_functional
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    {g : StrongDual ℝ V}
    (hsupport : ∀ p ∈ kktValueRegion Q f0 fi xStar, 0 ≤ g p)
    (hμ_pos : 0 < g ((0 : Λ), (1 : ℝ))) :
    ∀ x : E, x ∈ Q →
      0 ≤ f0 x - f0 xStar +
        ∑ i : Fin m, (g (kktBasis i, (0 : ℝ)) / g ((0 : Λ), (1 : ℝ))) * fi i x := by
  intro x hxQ
  have hmem :
      (((EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦ fi i x), f0 x - f0 xStar) ∈
        kktValueRegion Q f0 fi xStar := by
    exact ⟨x, hxQ, fun i ↦ le_rfl, le_rfl⟩
  have hsupp := hsupport _ hmem
  rw [strongDual_apply_kkt_product] at hsupp
  have hμ_ne : g ((0 : Λ), (1 : ℝ)) ≠ 0 := ne_of_gt hμ_pos
  have hdiv :
      0 ≤
        ((∑ i : Fin m, fi i x * g (kktBasis i, (0 : ℝ))) +
            (f0 x - f0 xStar) * g ((0 : Λ), (1 : ℝ))) /
          g ((0 : Λ), (1 : ℝ)) :=
    div_nonneg hsupp hμ_pos.le
  have hrewrite :
      ((∑ i : Fin m, fi i x * g (kktBasis i, (0 : ℝ))) +
          (f0 x - f0 xStar) * g ((0 : Λ), (1 : ℝ))) /
        g ((0 : Λ), (1 : ℝ)) =
        f0 x - f0 xStar +
          ∑ i : Fin m, (g (kktBasis i, (0 : ℝ)) / g ((0 : Λ), (1 : ℝ))) * fi i x := by
    calc
      ((∑ i : Fin m, fi i x * g (kktBasis i, (0 : ℝ))) +
          (f0 x - f0 xStar) * g ((0 : Λ), (1 : ℝ))) /
        g ((0 : Λ), (1 : ℝ))
          =
            (∑ i : Fin m, fi i x * g (kktBasis i, (0 : ℝ))) /
                g ((0 : Λ), (1 : ℝ)) +
              ((f0 x - f0 xStar) * g ((0 : Λ), (1 : ℝ))) / g ((0 : Λ), (1 : ℝ)) := by
            rw [add_div]
      _ =
            (∑ i : Fin m,
              (g (kktBasis i, (0 : ℝ)) / g ((0 : Λ), (1 : ℝ))) * fi i x) +
              (f0 x - f0 xStar) := by
            rw [Finset.sum_div]
            congr 1
            · refine Finset.sum_congr rfl fun i hi ↦ ?_
              field_simp [hμ_ne]
            · field_simp [hμ_ne]
      _ = f0 x - f0 xStar +
            ∑ i : Fin m,
              (g (kktBasis i, (0 : ℝ)) / g ((0 : Λ), (1 : ℝ))) * fi i x := by
            ring
  simpa [hrewrite] using hdiv

/-- Helper for Theorem 3.1.26: primal feasibility at `xStar` lets the Hahn--Banach support route
produce the normalized weighted inequality and complementary slackness. -/
-- Proof sketch: support the convex value region at the boundary point `0`, normalize the
-- supporting functional by its positive scalar coefficient, then apply the resulting inequality
-- at `xStar` to recover complementary slackness.
theorem exists_normalized_weighted_value_inequality_of_feasible
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    (hopt : IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar)
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi)
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    ∃ lam : Λ,
      lam ∈ ℝ₊^m ∧
        (∀ x : E, x ∈ Q →
          0 ≤ f0 x - f0 xStar + ∑ i : Fin m, lam i * fi i x) ∧
        ∀ i : Fin m, lam i * fi i xStar = 0 := by
  have hValueConvex :
      Convex ℝ (kktValueRegion Q f0 fi xStar) :=
    kkt_value_region_convex hf0_conv hfi_conv
  have hZeroMem :
      ((0 : Λ), (0 : ℝ)) ∈ kktValueRegion Q f0 fi xStar :=
    zero_mem_kktValueRegion_of_feasible hxStar
  have hIntNonempty :
      (interior (kktValueRegion Q f0 fi xStar)).Nonempty :=
    kktValueRegion_interior_nonempty_of_slater hSlater
  have hZeroNotInterior :
      ((0 : Λ), (0 : ℝ)) ∉ interior (kktValueRegion Q f0 fi xStar) :=
    zero_not_mem_interior_kktValueRegion hopt
  obtain ⟨f, hf_ne, hf_support⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hValueConvex hZeroNotInterior hIntNonempty
  let g : StrongDual ℝ V := -f
  have hg_ne : g ≠ 0 := by
    intro hg_zero
    exact hf_ne (by simpa [g] using hg_zero)
  have hsupport : ∀ p ∈ kktValueRegion Q f0 fi xStar, 0 ≤ g p := by
    intro p hp
    -- Negating the separator turns the support inequality at `0` into the lower bound we need.
    have hbase : g ((0 : Λ), (0 : ℝ)) ≤ g p := by
      simpa [g] using neg_le_neg (hf_support p hp)
    have hzero : g ((0 : Λ), (0 : ℝ)) = 0 := by
      change g (0 : V) = 0
      exact map_zero g
    simpa [hzero] using hbase
  obtain ⟨hcoord_nonneg, hμ_pos⟩ :=
    kkt_supporting_coefficients_nonnegative_and_scalar_pos hg_ne hsupport hxStar hSlater
  let lam : Λ :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm
      (fun i ↦ g (kktBasis i, (0 : ℝ)) / g ((0 : Λ), (1 : ℝ)))
  have hlam_apply :
      ∀ i : Fin m, lam i = g (kktBasis i, (0 : ℝ)) / g ((0 : Λ), (1 : ℝ)) := by
    intro i
    simp [lam, kktBasis]
  have hlam_nonneg : lam ∈ ℝ₊^m := by
    rw [EuclideanSpace.mem_nonnegativeOrthant_iff]
    intro i
    rw [hlam_apply i]
    exact div_nonneg (hcoord_nonneg i) hμ_pos.le
  have hvalue :
      ∀ x : E, x ∈ Q →
        0 ≤ f0 x - f0 xStar + ∑ i : Fin m, lam i * fi i x := by
    intro x hxQ
    simpa [hlam_apply] using
      weighted_value_inequality_of_supporting_functional hsupport hμ_pos x hxQ
  have hlam_nonneg' : ∀ i : Fin m, 0 ≤ lam i := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hlam_nonneg
  have hcomp : ∀ i : Fin m, lam i * fi i xStar = 0 := by
    have hvalue_xStar :
        0 ≤ ∑ i : Fin m, lam i * fi i xStar := by
      simpa using hvalue xStar hxStar.1
    have hsum_nonpos :
        ∑ i : Fin m, lam i * fi i xStar ≤ 0 := by
      refine Finset.sum_nonpos fun i _ ↦ ?_
      exact mul_nonpos_of_nonneg_of_nonpos (hlam_nonneg' i) (hxStar.2 i)
    have hsum_eq_zero :
        ∑ i : Fin m, lam i * fi i xStar = 0 :=
      le_antisymm hsum_nonpos hvalue_xStar
    intro i
    have hterm_nonneg :
        ∀ j ∈ (Finset.univ : Finset (Fin m)), 0 ≤ -(lam j * fi j xStar) := by
      intro j hj
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hlam_nonneg' j) (hxStar.2 j))
    have hneg_sum_eq_zero :
        ∑ j : Fin m, -(lam j * fi j xStar) = 0 := by
      simpa [Finset.sum_neg_distrib] using congrArg Neg.neg hsum_eq_zero
    have hterm_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hneg_sum_eq_zero i (by simp)
    linarith
  exact ⟨lam, hlam_nonneg, hvalue, hcomp⟩

/-- Helper for Theorem 3.1.26: the strict negative orthant in `Λ × ℝ` is convex. -/
-- Proof sketch: every coordinate of a convex combination of strictly negative vectors remains
-- strictly negative.
theorem kkt_negativeRegion_convex :
    Convex ℝ (kktNegativeRegion : Set V) := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · -- Every coordinate of the convex combination remains strictly negative.
    intro i
    have hcomb : a * p.1 i + b * q.1 i < 0 := by
      by_cases ha_zero : a = 0
      · have hb_one : b = 1 := by linarith
        simpa [ha_zero, hb_one] using hq.1 i
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
        have hfirst : a * p.1 i < 0 := mul_neg_of_pos_of_neg ha_pos (hp.1 i)
        have hsecond : b * q.1 i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (hq.1 i).le
        have hsum : a * p.1 i + b * q.1 i < 0 + 0 :=
          add_lt_add_of_lt_of_le hfirst hsecond
        simpa using hsum
    simpa [smul_eq_mul] using hcomb
  · -- The scalar component is handled by the same strict-negativity calculation.
    have hcomb : a * p.2 + b * q.2 < 0 := by
      by_cases ha_zero : a = 0
      · have hb_one : b = 1 := by linarith
        simpa [ha_zero, hb_one] using hq.2
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
        have hfirst : a * p.2 < 0 := mul_neg_of_pos_of_neg ha_pos hp.2
        have hsecond : b * q.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hq.2.le
        have hsum : a * p.2 + b * q.2 < 0 + 0 :=
          add_lt_add_of_lt_of_le hfirst hsecond
        simpa using hsum
    simpa [smul_eq_mul] using hcomb

/-- Helper for Theorem 3.1.26: finite sums of nonnegative multiples of the constraint functions
remain convex on `Q`. -/
-- Proof sketch: apply `ConvexOn.smul` to each constraint and combine the resulting convex
-- summands inductively with `ConvexOn.add`.
theorem convexOn_finset_weighted_constraint_sum
    {Q : Set E} {fi : Fin m → E → ℝ} {lam : Λ}
    (hQ_conv : Convex ℝ Q)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    (s : Finset (Fin m))
    (hlam_nonneg : ∀ i ∈ s, 0 ≤ lam i) :
    ConvexOn ℝ Q (fun x ↦ Finset.sum s fun i ↦ lam i * fi i x) := by
  -- Route correction: when `s = ∅`, the sum is the constant zero function, so we need the
  -- ambient convexity of `Q` explicitly rather than trying to recover it from a missing index.
  revert hlam_nonneg
  refine Finset.induction_on s ?_ ?_
  · intro _
    -- The empty weighted sum is the constant zero function.
    simpa using (convexOn_const (0 : ℝ) hQ_conv)
  · intro i s his hih hlam_nonneg
    have hi_nonneg : 0 ≤ lam i := hlam_nonneg i (Finset.mem_insert_self i s)
    have hi_conv : ConvexOn ℝ Q (fun x ↦ lam i * fi i x) :=
      (hfi_conv i).smul hi_nonneg
    have hs_nonneg : ∀ j ∈ s, 0 ≤ lam j := by
      intro j hj
      exact hlam_nonneg j (Finset.mem_insert_of_mem hj)
    have hs_conv : ConvexOn ℝ Q (fun x ↦ Finset.sum s fun j ↦ lam j * fi j x) :=
      hih hs_nonneg
    -- Add the new weighted constraint term to the convex tail sum.
    simpa [Finset.sum_insert his, add_comm, add_left_comm, add_assoc] using hi_conv.add hs_conv

/-- Helper for Theorem 3.1.26: the weighted Lagrangian is convex on `Q` for every nonnegative
multiplier vector. -/
-- Proof sketch: combine convexity of `f0` with the preceding finite-sum convexity lemma for the
-- weighted constraint contribution.
theorem weighted_lagrangian_convexOn
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {lam : Λ}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    (hlam_nonneg : lam ∈ ℝ₊^m) :
    ConvexOn ℝ Q (weightedLagrangian f0 fi lam) := by
  have hlam_nonneg' : ∀ i : Fin m, 0 ≤ lam i := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hlam_nonneg
  have hsum_conv :
      ConvexOn ℝ Q (fun x ↦ ∑ i : Fin m, lam i * fi i x) :=
    convexOn_finset_weighted_constraint_sum hf0_conv.1 hfi_conv Finset.univ
      (fun i _ ↦ hlam_nonneg' i)
  -- The weighted Lagrangian is the sum of the convex objective and the convex weighted
  -- constraint contribution.
  simpa [weightedLagrangian] using hf0_conv.add hsum_conv

/-- Helper for Theorem 3.1.26: finite sums of weighted gradients add in the expected Euclidean
form. -/
-- Proof sketch: differentiate each scalar multiple `lam i * fi i`, sum the Fréchet derivatives,
-- and then convert the resulting dual-space sum back to a gradient vector.
theorem hasGradientAt_finset_weighted_constraint_sum
    {fi : Fin m → E → ℝ} {xStar : E} (hfi_diff : ∀ i : Fin m, DifferentiableAt ℝ (fi i) xStar)
    (s : Finset (Fin m)) (lam : Λ) :
    HasGradientAt (fun x ↦ Finset.sum s fun i ↦ lam i * fi i x)
      (Finset.sum s fun i ↦ (lam i) • ∇ (fi i) xStar) xStar := by
  have hsum :
      HasFDerivAt (fun x ↦ Finset.sum s fun i ↦ lam i * fi i x)
        (Finset.sum s fun i ↦ (lam i) • InnerProductSpace.toDual ℝ E (∇ (fi i) xStar)) xStar := by
    -- Differentiate each weighted constraint term and sum the resulting Fréchet derivatives.
    refine HasFDerivAt.fun_sum ?_
    intro i hi
    simpa [smul_eq_mul] using
      ((hfi_diff i).hasGradientAt.hasFDerivAt.const_smul (lam i))
  have hsum' :
      HasFDerivAt (fun x ↦ Finset.sum s fun i ↦ lam i * fi i x)
        (InnerProductSpace.toDual ℝ E (Finset.sum s fun i ↦ (lam i) • ∇ (fi i) xStar)) xStar := by
    simpa using hsum
  simpa using hsum'.hasGradientAt

/-- Helper for Theorem 3.1.26: the weighted Lagrangian has the expected gradient at `xStar`. -/
-- Proof sketch: add the gradient of `f0` to the finite sum of the weighted constraint
-- gradients.
theorem weighted_lagrangian_hasGradientAt
    {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E} (hf0_diff : DifferentiableAt ℝ f0 xStar)
    (hfi_diff : ∀ i : Fin m, DifferentiableAt ℝ (fi i) xStar) (lam : Λ) :
    HasGradientAt (weightedLagrangian f0 fi lam)
      (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar) xStar := by
  have hf0_grad : HasGradientAt f0 (∇ f0 xStar) xStar := hf0_diff.hasGradientAt
  have hconstraint :
      HasFDerivAt (fun x ↦ ∑ i : Fin m, lam i * fi i x)
        (InnerProductSpace.toDual ℝ E (∑ i : Fin m, (lam i) • ∇ (fi i) xStar)) xStar :=
    (hasGradientAt_finset_weighted_constraint_sum hfi_diff Finset.univ lam).hasFDerivAt
  have htotal :
      HasFDerivAt (weightedLagrangian f0 fi lam)
        (InnerProductSpace.toDual ℝ E (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar))
          xStar := by
    -- Differentiate the objective and weighted constraint sum separately, then add.
    simpa [weightedLagrangian] using hf0_grad.hasFDerivAt.add hconstraint
  simpa using htotal.hasGradientAt

/-- Helper for Theorem 3.1.26: complementary slackness makes the weighted Lagrangian agree with
the objective at the certificate point. -/
-- Proof sketch: every weighted constraint term vanishes, so the finite sum in the Lagrangian is
-- zero.
theorem weighted_lagrangian_eq_objective_of_complementary_slackness
    {f0 : E → ℝ} {fi : Fin m → E → ℝ} {lam : Λ} {x : E}
    (hcomp : ∀ i : Fin m, lam i * fi i x = 0) :
    weightedLagrangian f0 fi lam x = f0 x := by
  simp [weightedLagrangian, hcomp]

/-- Helper for Theorem 3.1.26: the scalar weighted inequality and complementary slackness imply
the Lagrangian variational inequality on `Q`. -/
-- Proof sketch: first read the scalar inequality as `xStar` minimizing the weighted Lagrangian on
-- `Q`, then invoke the Chapter 2 first-order optimality theorem for that convex differentiable
-- objective.
theorem weighted_value_inequality_implies_variational_inequality
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    (hf0_diff : DifferentiableAt ℝ f0 xStar)
    (hfi_diff : ∀ i : Fin m, DifferentiableAt ℝ (fi i) xStar)
    {lam : Λ}
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi)
    (hlam_nonneg : lam ∈ ℝ₊^m)
    (hvalue :
      ∀ x : E, x ∈ Q →
        0 ≤ f0 x - f0 xStar + ∑ i : Fin m, lam i * fi i x)
    (hcomp : ∀ i : Fin m, lam i * fi i xStar = 0) :
    ∀ x : E, x ∈ Q →
      0 ≤
        inner ℝ
          (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar)
          (x - xStar) := by
  have hLagMin : IsMinOn (weightedLagrangian f0 fi lam) Q xStar := by
    rw [isMinOn_iff]
    intro x hxQ
    have hvalue' := hvalue x hxQ
    have hstar_eq :
        weightedLagrangian f0 fi lam xStar = f0 xStar :=
      weighted_lagrangian_eq_objective_of_complementary_slackness hcomp
    have hx_lower : f0 xStar ≤ weightedLagrangian f0 fi lam x := by
      have : f0 xStar ≤ f0 x + ∑ i : Fin m, lam i * fi i x := by
        linarith
      simpa [weightedLagrangian, add_comm, add_left_comm, add_assoc] using this
    simpa [hstar_eq] using hx_lower
  -- Apply the Chapter 2 first-order optimality theorem to the weighted Lagrangian.
  exact
    (ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt
      (weighted_lagrangian_convexOn hf0_conv hfi_conv hlam_nonneg)
      hxStar.1
      (weighted_lagrangian_hasGradientAt hf0_diff hfi_diff lam)).1 hLagMin

/-- Helper for Theorem 3.1.26: a KKT certificate implies primal optimality. -/
-- Proof sketch: the variational inequality makes `xStar` minimize the weighted Lagrangian on
-- `Q`; complementary slackness identifies its value at `xStar` with `f0 xStar`, while feasibility
-- and multiplier nonnegativity show the weighted Lagrangian never exceeds `f0` on feasible
-- points.
theorem isMinOn_of_kkt_certificate
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    (hf0_diff : DifferentiableAt ℝ f0 xStar)
    (hfi_diff : ∀ i : Fin m, DifferentiableAt ℝ (fi i) xStar)
    {lam : Λ}
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi)
    (hlam_nonneg : lam ∈ ℝ₊^m)
    (hvari :
      ∀ x : E, x ∈ Q →
        0 ≤
          inner ℝ
            (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar)
            (x - xStar))
    (hcomp : ∀ i : Fin m, lam i * fi i xStar = 0) :
    IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar := by
  have hLagMin : IsMinOn (weightedLagrangian f0 fi lam) Q xStar := by
    exact
      (ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt
        (weighted_lagrangian_convexOn hf0_conv hfi_conv hlam_nonneg)
        hxStar.1
        (weighted_lagrangian_hasGradientAt hf0_diff hfi_diff lam)).2 hvari
  have hlam_nonneg' : ∀ i : Fin m, 0 ≤ lam i := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hlam_nonneg
  rw [isMinOn_iff]
  intro x hxFeas
  have hLagLe :
      weightedLagrangian f0 fi lam x ≤ f0 x := by
    have hsum_nonpos : ∑ i : Fin m, lam i * fi i x ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (hlam_nonneg' i) (hxFeas.2 i)
    dsimp [weightedLagrangian]
    linarith
  have hstar_eq :
      weightedLagrangian f0 fi lam xStar = f0 xStar :=
    weighted_lagrangian_eq_objective_of_complementary_slackness hcomp
  -- Compare feasible points through the weighted Lagrangian, then drop the nonpositive
  -- constraint contribution.
  calc
    f0 xStar = weightedLagrangian f0 fi lam xStar := by
      symm
      exact hstar_eq
    _ ≤ weightedLagrangian f0 fi lam x := (isMinOn_iff.mp hLagMin) x hxFeas.1
    _ ≤ f0 x := hLagLe

/-- Helper for Theorem 3.1.26: the forward KKT direction reduces to separating the strict
negative orthant from the convex value region and normalizing the separating functional. -/
-- Route correction: the easy part of the forward implication is now factored out into
-- `kkt_value_region_convex`, `kkt_negative_region_disjoint`, and the weighted-Lagrangian closing
-- lemmas below. The only remaining blocker is the separator-normalization step that extracts the
-- nonnegative multiplier vector with `μ > 0` from Hahn--Banach.
-- TODO: apply geometric Hahn--Banach to `kktNegativeRegion` and `kktValueRegion Q f0 fi xStar`,
-- use `((0 : Λ), 0) ∈ kktValueRegion ...` and small negative points to force the separating level
-- to zero, prove coordinatewise nonnegativity of the separator, rule out `μ = 0` with the Slater
-- point, and divide by `μ`.
theorem exists_normalized_weighted_value_inequality
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ} {xStar : E}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    (hopt : IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar)
    (hxStar : xStar ∈ inequalityConstrainedFeasibleSet Q fi)
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    ∃ lam : Λ,
      lam ∈ ℝ₊^m ∧
        (∀ x : E, x ∈ Q →
          0 ≤ f0 x - f0 xStar + ∑ i : Fin m, lam i * fi i x) ∧
        ∀ i : Fin m, lam i * fi i xStar = 0 := by
  -- Repackage the explicit feasibility data into the helper theorem that already performs the
  -- Hahn--Banach support and normalization steps.
  exact
    exists_normalized_weighted_value_inequality_of_feasible
      hf0_conv hfi_conv hopt hxStar hSlater

/-- Theorem 3.1.26: (Karush--Kuhn--Tucker) under convexity, ambient differentiability at every
point of `Q`, and a
strict-feasibility point for the constraints, a point `xStar` is an optimal solution of the
inequality-constrained problem `min {f₀(x) | x ∈ Q, fᵢ(x) ≤ 0 for all i}` if and only if there is
a nonnegative multiplier vector such that `xStar` is primal feasible, the canonical gradients
`∇ f0 xStar` and `∇ (fi i) xStar` yield the Lagrangian variational inequality on `Q`, and the
coordinates obey complementary slackness at `xStar`. -/
-- Proof sketch: rewrite the problem as minimizing `f₀` on
-- `inequalityConstrainedFeasibleSet Q fi`, while keeping primal feasibility explicit on the
-- source-facing surface. The forward direction comes from the convex
-- first-order optimality condition together with the max/subdifferential description of the active
-- inequality constraints under the Chapter 1 Slater condition for the restricted subtype problem,
-- which yields a multiplier vector. For the reverse direction, use the `ConvexOn` hypotheses on
-- `f₀` and `fᵢ`, the variational inequality, and
-- complementary slackness to recover the optimality inequality against every feasible point.
theorem isMinOn_iff_exists_karush_kuhn_tucker_multiplier
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    {xStar : E}
    (hf0_diff : ∀ x ∈ Q, DifferentiableAt ℝ f0 x)
    (hfi_diff : ∀ i : Fin m, ∀ x ∈ Q, DifferentiableAt ℝ (fi i) x)
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    (xStar ∈ Q ∧
        (∀ i : Fin m, fi i xStar ≤ 0) ∧
        IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar) ↔
      ∃ lam : Λ,
        lam ∈ ℝ₊^m ∧
          xStar ∈ Q ∧
          (∀ i : Fin m, fi i xStar ≤ 0) ∧
          (∀ x : E, x ∈ Q →
            0 ≤
              inner ℝ
                (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar)
                (x - xStar)) ∧
          ∀ i : Fin m, lam i * fi i xStar = 0 := by
  constructor
  · rintro ⟨hxStarQ, hxStarFi, hopt⟩
    have hxStarFeas : xStar ∈ inequalityConstrainedFeasibleSet Q fi := by
      -- Package the explicit primal feasibility data in the canonical feasible-set predicate.
      exact mem_inequalityConstrainedFeasibleSet_iff.2 ⟨hxStarQ, hxStarFi⟩
    obtain ⟨lam, hlam_nonneg, hvalue, hcomp⟩ :=
      exists_normalized_weighted_value_inequality hf0_conv hfi_conv hopt hxStarFeas hSlater
    have hvari :
        ∀ x : E, x ∈ Q →
          0 ≤
            inner ℝ
              (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar)
              (x - xStar) := by
      -- Convert the scalar weighted inequality into the gradient variational inequality.
      exact
        weighted_value_inequality_implies_variational_inequality
          hf0_conv
          hfi_conv
          (hf0_diff xStar hxStarQ)
          (fun i ↦ hfi_diff i xStar hxStarQ)
          hxStarFeas
          hlam_nonneg
          hvalue
          hcomp
    exact ⟨lam, hlam_nonneg, hxStarQ, hxStarFi, hvari, hcomp⟩
  · rintro ⟨lam, hlam_nonneg, hxStarQ, hxStarFi, hvari, hcomp⟩
    have hxStarFeas : xStar ∈ inequalityConstrainedFeasibleSet Q fi := by
      -- Rebuild the feasible-set witness needed by the reverse KKT implication.
      exact mem_inequalityConstrainedFeasibleSet_iff.2 ⟨hxStarQ, hxStarFi⟩
    refine ⟨hxStarQ, hxStarFi, ?_⟩
    -- Apply the weighted-Lagrangian optimality theorem to recover primal optimality.
    exact
      isMinOn_of_kkt_certificate
        hf0_conv
        hfi_conv
        (hf0_diff xStar hxStarQ)
        (fun i ↦ hfi_diff i xStar hxStarQ)
        hxStarFeas
        hlam_nonneg
        hvari
        hcomp

end

end
