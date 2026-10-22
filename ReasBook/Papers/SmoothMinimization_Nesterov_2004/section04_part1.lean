/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section02
import Papers.SmoothMinimization_Nesterov_2004.section03

open scoped NNReal

/-- `OperatorNormDef` is nonnegative. -/
lemma operatorNormDef_nonneg {E1 E2 : Type*} [SeminormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [SeminormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) : 0 ≤ OperatorNormDef A := by
  classical
  set S : Set ℝ :=
      { r : ℝ | ∃ x : E1, ∃ u : E2, ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A x) u } with hSdef
  -- rewrite the definition in terms of the auxiliary set `S`
  have hOp : OperatorNormDef A = sSup S := by
    unfold OperatorNormDef
    rw [hSdef.symm]
  by_cases hS : S = ∅
  · -- empty-set case: `sSup ∅ = 0`
    have : (OperatorNormDef A) = 0 := by
      simp [hOp, hS, Real.sSup_empty]
    simp [this]
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.2 hS
    rcases hSne with ⟨r, hr⟩
    have hneg : (-r) ∈ S := by
      rcases hr with ⟨x, u, hx, hu, rfl⟩
      refine ⟨x, -u, hx, ?_, ?_⟩
      · simpa [norm_neg] using hu
      · simp [DualPairing]
    have hex : ∃ t ∈ S, 0 ≤ t := by
      by_cases hr0 : 0 ≤ r
      · exact ⟨r, hr, hr0⟩
      · have : 0 ≤ -r := by linarith
        exact ⟨-r, hneg, this⟩
    have : 0 ≤ sSup S := Real.sSup_nonneg' hex
    simpa [hOp] using this

/-- Definition 1.4.1.
Assume `fhat : E1 → ℝ` is convex and continuously differentiable on `Q1`, and its gradient is
Lipschitz on `Q1` with constant `M ≥ 0` in the dual norm:
`‖∇ fhat x - ∇ fhat y‖_{1,*} ≤ M ‖x - y‖_1` for all `x, y ∈ Q1`.
Let `f_μ` be the smoothed function from (2.5). Define the smoothed objective
`\bar f_μ(x) = fhat x + f_μ x` and consider `min_{x ∈ Q1} \bar f_μ(x)` (equation (4.1)). -/
noncomputable def SmoothedObjective {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ : ℝ) (fhat : E1 → ℝ) : E1 → ℝ :=
  fun x => fhat x + SmoothedMaxFunction Q2 A phihat d2 μ x

/-- LipschitzOnWith is preserved under pointwise addition. -/
lemma lipschitzOnWith_add {α β : Type*} [PseudoMetricSpace α] [NormedAddCommGroup β]
    {K₁ K₂ : ℝ≥0} {f g : α → β} {s : Set α}
    (hf : LipschitzOnWith K₁ f s) (hg : LipschitzOnWith K₂ g s) :
    LipschitzOnWith (K₁ + K₂) (fun x => f x + g x) s := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hf' := hf.dist_le_mul x hx y hy
  have hg' := hg.dist_le_mul x hx y hy
  have hdist :
      dist (f x + g x) (f y + g y) ≤ dist (f x) (f y) + dist (g x) (g y) := by
    calc
      dist (f x + g x) (f y + g y)
          = ‖(f x + g x) - (f y + g y)‖ := by simp [dist_eq_norm]
      _ = ‖(f x - f y) + (g x - g y)‖ := by
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
      _ = dist (f x) (f y) + dist (g x) (g y) := by simp [dist_eq_norm]
  calc
    dist (f x + g x) (f y + g y) ≤ dist (f x) (f y) + dist (g x) (g y) := hdist
    _ ≤ (K₁ : ℝ) * dist x y + (K₂ : ℝ) * dist x y := by
        exact add_le_add hf' hg'
    _ = (K₁ + K₂) * dist x y := by simp [add_mul]

/-- Lipschitz bound for the derivative of the smoothed max-function on a set. -/
lemma smoothedMaxFunction_fderiv_lipschitzOn {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q1 : Set E1) (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ σ2 : ℝ)
    (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    (∀ x,
        HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) →
    (∀ x1 x2,
        μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2)) →
    LipschitzOnWith (Real.toNNReal ((1 / (μ * σ2)) * (OperatorNormDef A') ^ 2))
      (fun x => fderiv ℝ fμ x) Q1 := by
  classical
  simp only
  intro _ _
  set fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  set A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  have hprops :
      ContDiff ℝ (1 : ℕ∞) fμ ∧
        ConvexOn ℝ Set.univ fμ ∧
          (∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) ∧
            ∃ Lμ : ℝ,
              Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
                LipschitzWith (Real.toNNReal Lμ)
                  (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
    simpa [fμ, A'] using
      (smoothedMaxFunction_properties (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
        (μ := μ) (σ2 := σ2) (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (uμ := uμ)
        (hmax := hmax))
  rcases hprops with ⟨_, _, hderiv, ⟨Lμ, hLμ, hLip⟩⟩
  have hderiv' :
      (fun x => fderiv ℝ fμ x) =
        fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap := by
    funext x
    exact (hderiv x).fderiv
  have hLipOn :
      LipschitzOnWith (Real.toNNReal Lμ) (fun x => fderiv ℝ fμ x) Q1 := by
    simpa [hderiv'] using (hLip.lipschitzOnWith (s := Q1))
  simpa [hLμ] using hLipOn

/-- On a set, the derivative of a sum is the sum of derivatives. -/
lemma fderiv_add_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {s : Set E}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ s, DifferentiableAt ℝ g x) :
    ∀ x ∈ s, fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x := by
  intro x hx
  simpa using (fderiv_add (f := f) (g := g) (x := x) (hf := hf x hx) (hg := hg x hx))

/-- `Real.toNNReal` preserves addition on nonnegative inputs. -/
lemma toNNReal_add_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.toNNReal (a + b) = Real.toNNReal a + Real.toNNReal b := by
  simpa using (Real.toNNReal_add ha hb)

/-- Proposition 1.4.1.
Under the assumptions of Definition 1.4.1, the function `\bar f_μ` has Lipschitz continuous
gradient on `Q1` with Lipschitz constant `L_μ := M + (1/(μ σ2)) ‖A‖_{1,2}^2` (equation (4.2)),
where `σ2` is the strong convexity parameter of the prox-function `d2` on `Q2`. -/
theorem smoothedObjective_lipschitz_gradient {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q1 : Set E1) (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ σ2 M : ℝ)
    (fhat : E1 → ℝ) (uμ : E1 → E2) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hM : 0 ≤ M)
    (hconv : StrongConvexOn Q2 σ2 d2)
    (hFhatDiff : ∀ x ∈ Q1, DifferentiableAt ℝ fhat x)
    (hLipschitz : LipschitzOnWith (Real.toNNReal M) (fun x => fderiv ℝ fhat x) Q1) :
    let fbar : E1 → ℝ := SmoothedObjective Q2 A phihat d2 μ fhat
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    (∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) →
    (∀ x,
        HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) →
    (∀ x1 x2,
        μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2)) →
    ∃ Lμ : ℝ,
      Lμ = M + (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
        LipschitzOnWith (Real.toNNReal Lμ) (fun x => fderiv ℝ fbar x) Q1 := by
  classical
  have hconv' := hconv
  simp only
  intro hmax hDanskin hcoercive
  set fbar : E1 → ℝ := SmoothedObjective Q2 A phihat d2 μ fhat with hfbar
  set fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  set A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp } with hA'
  have hDanskin' :
      ∀ x,
        HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
    simpa [hA'.symm] using hDanskin
  have hcoercive' :
      ∀ x1 x2,
        μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2) := by
    simpa [hA'.symm] using hcoercive
  set L2 : ℝ := (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2
  have hLipμ :
      LipschitzOnWith (Real.toNNReal L2) (fun x => fderiv ℝ fμ x) Q1 := by
    simpa [fμ, A', L2] using
      (smoothedMaxFunction_fderiv_lipschitzOn (Q1 := Q1) (Q2 := Q2) (A := A)
        (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2) (hμ := hμ) (hσ2 := hσ2)
        (hconv := hconv') (uμ := uμ) (hmax := hmax) hDanskin' hcoercive')
  have hFμDiff : ∀ x, DifferentiableAt ℝ fμ x := by
    have hprops :
        ContDiff ℝ (1 : ℕ∞) fμ ∧
          ConvexOn ℝ Set.univ fμ ∧
            (∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) ∧
              ∃ Lμ : ℝ,
                Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
                  LipschitzWith (Real.toNNReal Lμ)
                    (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
      simpa [fμ, A'] using
        (smoothedMaxFunction_properties (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
          (μ := μ) (σ2 := σ2) (hμ := hμ) (hσ2 := hσ2) (hconv := hconv') (uμ := uμ)
          (hmax := hmax))
    intro x
    exact (hprops.2.2.1 x).differentiableAt
  have hLipSum :
      LipschitzOnWith (Real.toNNReal M + Real.toNNReal L2)
        (fun x => fderiv ℝ fhat x + fderiv ℝ fμ x) Q1 := by
    simpa using
      (lipschitzOnWith_add (f := fun x => fderiv ℝ fhat x) (g := fun x => fderiv ℝ fμ x)
        hLipschitz hLipμ)
  have hL2_nonneg : 0 ≤ L2 := by
    have hμσ : 0 ≤ μ * σ2 := mul_nonneg (le_of_lt hμ) (le_of_lt hσ2)
    have hμσ' : 0 ≤ 1 / (μ * σ2) := by
      have : 0 ≤ (μ * σ2)⁻¹ := inv_nonneg.mpr hμσ
      simpa [one_div] using this
    have hsq : 0 ≤ (OperatorNormDef A') ^ 2 := by
      exact sq_nonneg (OperatorNormDef A')
    exact mul_nonneg hμσ' hsq
  have hLipSum' :
      LipschitzOnWith (Real.toNNReal (M + L2))
        (fun x => fderiv ℝ fhat x + fderiv ℝ fμ x) Q1 := by
    have hsum : Real.toNNReal (M + L2) = Real.toNNReal M + Real.toNNReal L2 := by
      simpa using (toNNReal_add_nonneg hM hL2_nonneg)
    simpa [hsum] using hLipSum
  have hderiv_add :
      ∀ x ∈ Q1, fderiv ℝ fbar x = fderiv ℝ fhat x + fderiv ℝ fμ x := by
    intro x hx
    have hf : DifferentiableAt ℝ fhat x := hFhatDiff x hx
    have hg : DifferentiableAt ℝ fμ x := hFμDiff x
    simpa [hfbar, fμ, SmoothedObjective] using
      (fderiv_add (f := fhat) (g := fμ) (x := x) (hf := hf) (hg := hg))
  have hLipBar :
      LipschitzOnWith (Real.toNNReal (M + L2)) (fun x => fderiv ℝ fbar x) Q1 := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hx' := hderiv_add x hx
    have hy' := hderiv_add y hy
    have hdist := hLipSum'.dist_le_mul x hx y hy
    simpa [hx', hy'] using hdist
  refine ⟨M + L2, by simp [L2], ?_⟩
  simpa [L2] using hLipBar

/-- Definition 1.4.2.
Let `Q1 ⊆ E1` be bounded, closed, and convex, and let `d1` be a prox-function on `Q1`, meaning
it is continuous and `σ1`-strongly convex on `Q1` for some `σ1 > 0` with respect to `‖·‖_1`.
Assume the (finite) prox-diameter bound `D1` satisfies
`max_{x ∈ Q1} d1 x ≤ D1 < +∞` (equation (4.3)). -/
def IsProxDiameterBound {E1 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    (Q1 : Set E1) (d1 : E1 → ℝ) (D1 : ℝ) : Prop :=
  ∀ x ∈ Q1, d1 x ≤ D1

/-- Linearization identity for the smoothed max-function under an adjoint derivative formula. -/
lemma smoothedMaxFunction_linearization {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (uμ : E1 → E2)
    (A' : E1 →ₗ[ℝ] Module.Dual ℝ E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x))
    (hderiv :
      ∀ x,
        fderiv ℝ (SmoothedMaxFunction Q2 A phihat d2 μ) x =
          (AdjointOperator A' (uμ x)).toContinuousLinearMap)
    (hpair : ∀ x u, DualPairing (AdjointOperator A' u) x = A x u) :
    ∀ x,
      SmoothedMaxFunction Q2 A phihat d2 μ x -
          DualPairing ((fderiv ℝ (SmoothedMaxFunction Q2 A phihat d2 μ) x).toLinearMap) x =
        -phihat (uμ x) - μ * d2 (uμ x) := by
  classical
  intro x
  set fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ with hfμ
  have hfx :
      fμ x = A x (uμ x) - phihat (uμ x) - μ * d2 (uμ x) := by
    have hmaxx := hmax x
    set g : E2 → ℝ := fun u => A x u - phihat u - μ * d2 u
    have hux : uμ x ∈ Q2 := hmaxx.1
    have hne : (g '' Q2).Nonempty := ⟨g (uμ x), ⟨uμ x, hux, rfl⟩⟩
    have hbd : BddAbove (g '' Q2) := by
      refine ⟨g (uμ x), ?_⟩
      rintro y ⟨v, hv, rfl⟩
      exact hmaxx.2 v hv
    have hsup_le : sSup (g '' Q2) ≤ g (uμ x) := by
      refine csSup_le hne ?_
      rintro y ⟨v, hv, rfl⟩
      exact hmaxx.2 v hv
    have hle_sup : g (uμ x) ≤ sSup (g '' Q2) := by
      refine le_csSup hbd ?_
      exact ⟨uμ x, hux, rfl⟩
    have hsup : sSup (g '' Q2) = g (uμ x) := le_antisymm hsup_le hle_sup
    calc
      fμ x = sSup (g '' Q2) := by simp [hfμ, SmoothedMaxFunction, g]
      _ = g (uμ x) := hsup
      _ = A x (uμ x) - phihat (uμ x) - μ * d2 (uμ x) := by simp [g]
  have hderiv' :
      ((fderiv ℝ fμ x).toLinearMap) = AdjointOperator A' (uμ x) := by
    have h := congrArg ContinuousLinearMap.toLinearMap (hderiv x)
    simpa [hfμ] using h
  calc
    fμ x - DualPairing ((fderiv ℝ fμ x).toLinearMap) x =
        (A x (uμ x) - phihat (uμ x) - μ * d2 (uμ x)) -
          DualPairing (AdjointOperator A' (uμ x)) x := by
      simp [hfx, hderiv']
    _ = -phihat (uμ x) - μ * d2 (uμ x) := by
      have hpairx : DualPairing (AdjointOperator A' (uμ x)) x = A x (uμ x) :=
        hpair x (uμ x)
      have hring :
          (A x (uμ x) - phihat (uμ x) - μ * d2 (uμ x)) - A x (uμ x) =
            -phihat (uμ x) - μ * d2 (uμ x) := by
        ring
      simpa [hpairx] using hring

/-- Strong convexity on a set implies the set is convex. -/
lemma convex_of_strongConvexOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {σ : ℝ} {f : E → ℝ} (h : StrongConvexOn s σ f) : Convex ℝ s :=
  h.1

/-- Weak duality: `f(x) ≥ φ(u)` for any `x ∈ Q1` and `u ∈ Q2`. -/
lemma adjointForm_duality_gap_nonneg {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q1 : Set E1) (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (fhat : E1 → ℝ) (phihat : E2 → ℝ)
    (hbd0 : ∀ x, BddAbove ((fun u => A x u - phihat u) '' Q2))
    (hbdBelow : ∀ u, BddBelow ((fun x => A x u + fhat x) '' Q1)) :
    ∀ x ∈ Q1, ∀ u : Q2,
      0 ≤ (fhat x + sSup ((fun u => A x u - phihat u) '' Q2)) -
        AdjointFormPotential Q1 Q2 A fhat phihat u := by
  classical
  intro x hx u
  have hsup :
      A x u - phihat u ≤ sSup ((fun u => A x u - phihat u) '' Q2) := by
    have hmem :
        A x u - phihat u ∈ ((fun u => A x u - phihat u) '' Q2) :=
      ⟨u, u.property, rfl⟩
    exact le_csSup (hbd0 x) hmem
  have hinf :
      sInf ((fun x => A x u + fhat x) '' Q1) ≤ A x u + fhat x := by
    have hmem :
        A x u + fhat x ∈ ((fun x => A x u + fhat x) '' Q1) :=
      ⟨x, hx, rfl⟩
    exact csInf_le (hbdBelow u) hmem
  have hAx : A x u ≤ sSup ((fun u => A x u - phihat u) '' Q2) + phihat u := by
    linarith [hsup]
  have hbound :
      sInf ((fun x => A x u + fhat x) '' Q1) ≤
        fhat x + sSup ((fun u => A x u - phihat u) '' Q2) + phihat u := by
    linarith [hinf, hAx]
  have hfinal :
      0 ≤ fhat x + sSup ((fun u => A x u - phihat u) '' Q2) + phihat u -
        sInf ((fun x => A x u + fhat x) '' Q1) := by
    linarith [hbound]
  -- unfold `φ` and conclude
  simpa [AdjointFormPotential, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using hfinal

/-- The smoothed objective upper-bounds the original objective up to `μ D2`. -/
lemma smoothedObjective_bound {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ)
    (hμ : 0 ≤ μ) (hd2_nonneg : ∀ u ∈ Q2, 0 ≤ d2 u)
    (hbdd0 : ∀ x, BddAbove ((fun u => A x u - phihat u) '' Q2))
    (hbdd_d2 : BddAbove (d2 '' Q2)) (fhat : E1 → ℝ) :
    ∀ x : E1,
      fhat x + sSup ((fun u => A x u - phihat u) '' Q2) ≤
        SmoothedObjective Q2 A phihat d2 μ fhat x + μ * sSup (d2 '' Q2) := by
  classical
  intro x
  set D2 : ℝ := sSup (d2 '' Q2)
  set f0 : E1 → ℝ := fun x => sSup ((fun u => A x u - phihat u) '' Q2)
  set fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  have hbounds :
      fμ x ≤ f0 x ∧ f0 x ≤ fμ x + μ * D2 := by
    simpa [D2, f0, fμ] using
      (smoothedMaxFunction_bounds (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ)
        (hμ := hμ) (hd2_nonneg := hd2_nonneg) (hbdd0 := hbdd0) (hbdd_d2 := hbdd_d2) x)
  have hle : f0 x ≤ fμ x + μ * D2 := hbounds.2
  have hle' : f0 x + fhat x ≤ fμ x + μ * D2 + fhat x :=
    add_le_add_left hle (fhat x)
  calc
    fhat x + f0 x ≤ fhat x + (fμ x + μ * D2) := by
      simpa [add_comm, add_left_comm, add_assoc] using hle'
    _ = (fhat x + fμ x) + μ * D2 := by ring
    _ = SmoothedObjective Q2 A phihat d2 μ fhat x + μ * D2 := by
      simp [SmoothedObjective, fμ]

/-- The supremum of a nonnegative function on a nonempty set is nonnegative. -/
lemma sSup_image_nonneg {α : Type*} (s : Set α) (f : α → ℝ) (hbd : BddAbove (f '' s))
    (hne : s.Nonempty) (hnonneg : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ sSup (f '' s) := by
  rcases hne with ⟨x, hx⟩
  have hxmem : f x ∈ f '' s := ⟨x, hx, rfl⟩
  have hle : f x ≤ sSup (f '' s) := le_csSup hbd hxmem
  exact le_trans (hnonneg x hx) hle

/-- `z_k` is chosen as a minimizer of the auxiliary function defining `ψ_k` (Definition 1.3.5). -/
axiom z_k_isMinOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f d : E → ℝ) (L σ : ℝ) (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) :
    IsMinOn
      (fun z : E =>
        (L / σ) * d z +
          Finset.sum (Finset.range (k + 1)) (fun i =>
            let xi : E := xSeq i
            α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (z - xi)))) Q
      (z_k Q f d L σ α xSeq k)

/-- Rate bound for the optimal scheme after bounding the prox term by `D`. -/
lemma fbar_rate_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ D : ℝ}
    (xSeq ySeq : ℕ → Q) (N : ℕ) (hL : 0 < L) (hσ : 0 < σ)
    (hAlg : OptimalSchemeAlgorithm Q f d L σ xSeq ySeq) (hD : IsProxDiameterBound Q d D) {x : E}
    (hx : x ∈ Q) :
    f (ySeq N : E) ≤
      (4 * L * D) / (σ * (((N : ℝ) + 1) * ((N : ℝ) + 2))) +
        (2 / (((N : ℝ) + 1) * ((N : ℝ) + 2))) *
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) *
              (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := by
  classical
  let α : ℕ → ℝ := fun i => ((i : ℝ) + 1) / 2
  set Fk : E → ℝ := fun z =>
    (L / σ) * d z +
      Finset.sum (Finset.range (N + 1)) (fun i =>
        let xi : E := xSeq i
        α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (z - xi)))
  have hopt :=
    (optimal_scheme_rate (xSeq := xSeq) (ySeq := ySeq) hAlg).1 N
  have hz_k :
      IsMinOn
        (fun z : E =>
          (L / σ) * d z +
            Finset.sum (Finset.range (N + 1)) (fun i =>
              let xi : E := xSeq i
              α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (z - xi)))) Q
        (z_k Q f d L σ α xSeq N) :=
    z_k_isMinOn Q f d L σ α xSeq N
  have hmin' := isMinOn_iff.mp hz_k
  have hpsi_eq : psi_k Q f d L σ α xSeq N = Fk (z_k Q f d L σ α xSeq N) := by
    have hleast :
        IsLeast (Fk '' Q) (Fk (z_k Q f d L σ α xSeq N)) := by
      refine ⟨?_, ?_⟩
      · exact ⟨z_k Q f d L σ α xSeq N, (z_k Q f d L σ α xSeq N).property, rfl⟩
      · intro b hb
        rcases hb with ⟨y, hy, rfl⟩
        exact hmin' y hy
    simpa [psi_k, Fk] using (IsLeast.csInf_eq hleast)
  have hpsi_le : psi_k Q f d L σ α xSeq N ≤ Fk x := by
    calc
      psi_k Q f d L σ α xSeq N = Fk (z_k Q f d L σ α xSeq N) := hpsi_eq
      _ ≤ Fk x := hmin' x hx
  have hcomp :
      (((N : ℝ) + 1) * ((N : ℝ) + 2) / 4) * f (ySeq N : E) ≤ Fk x := by
    exact le_trans hopt hpsi_le
  set denom : ℝ := ((N : ℝ) + 1) * ((N : ℝ) + 2)
  have hdenom_pos : 0 < denom := by
    have h1 : 0 < (N : ℝ) + 1 := by nlinarith
    have h2 : 0 < (N : ℝ) + 2 := by nlinarith
    simpa [denom] using mul_pos h1 h2
  have hcoef_nonneg : 0 ≤ (4 / denom) := by
    exact div_nonneg (by norm_num) (le_of_lt hdenom_pos)
  have hmul := mul_le_mul_of_nonneg_left hcomp hcoef_nonneg
  have hleft : (4 / denom) * (denom / 4) = (1 : ℝ) := by
    field_simp [denom, hdenom_pos.ne']
  have hmult' :
      f (ySeq N : E) ≤ (4 / denom) * Fk x := by
    simpa [hleft, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hdx : d x ≤ D := hD x hx
  have hLσ_nonneg : 0 ≤ L / σ := by
    exact div_nonneg (le_of_lt hL) (le_of_lt hσ)
  have hdx' : (L / σ) * d x ≤ (L / σ) * D := by
    exact mul_le_mul_of_nonneg_left hdx hLσ_nonneg
  have hsum_le :
      (L / σ) * d x +
          Finset.sum (Finset.range (N + 1)) (fun i =>
            let xi : E := xSeq i
            α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (x - xi))) ≤
        (L / σ) * D +
          Finset.sum (Finset.range (N + 1)) (fun i =>
            let xi : E := xSeq i
            α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (x - xi))) := by
    exact add_le_add_left hdx' _
  have hmult'' :=
    mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
  have hmult''' :
      (4 / denom) * Fk x ≤
        (4 / denom) * ((L / σ) * D) +
          (4 / denom) *
            Finset.sum (Finset.range (N + 1)) (fun i =>
              let xi : E := xSeq i
              α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (x - xi))) := by
    simpa [Fk, mul_add, add_assoc, add_left_comm, add_comm] using hmult''
  have hmain : f (ySeq N : E) ≤
      (4 / denom) * ((L / σ) * D) +
        (4 / denom) *
          Finset.sum (Finset.range (N + 1)) (fun i =>
            let xi : E := xSeq i
            α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (x - xi))) := by
    exact le_trans hmult' hmult'''
  have hmain' : f (ySeq N : E) ≤
      (4 / denom) * ((L / σ) * D) +
        (4 / denom) *
          Finset.sum (Finset.range (N + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := by
    simpa using hmain
  have hsum_alpha :
      (4 / denom) *
          Finset.sum (Finset.range (N + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) =
        (2 / denom) *
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) *
              (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := by
    have hsum' :
        Finset.sum (Finset.range (N + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) =
          (Finset.sum (Finset.range (N + 1)) (fun i =>
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))) *
            (1 / 2 : ℝ) := by
      have hterm :
          ∀ i,
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)) =
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)) * (1 / 2 : ℝ) := by
        intro i
        simp [α, div_eq_mul_inv, mul_assoc, mul_comm]
      calc
        Finset.sum (Finset.range (N + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) =
            Finset.sum (Finset.range (N + 1)) (fun i =>
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)) * (1 / 2 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i
        _ =
            (Finset.sum (Finset.range (N + 1)) (fun i =>
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))) *
              (1 / 2 : ℝ) := by
          symm
          simpa using (Finset.sum_mul (s := Finset.range (N + 1))
            (f := fun i =>
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))
            (a := (1 / 2 : ℝ)))
    calc
      (4 / denom) *
          Finset.sum (Finset.range (N + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) =
          (4 / denom) *
            ((Finset.sum (Finset.range (N + 1)) (fun i =>
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))) *
                (1 / 2 : ℝ)) := by
        simp [hsum']
      _ =
          (2 / denom) *
            Finset.sum (Finset.range (N + 1)) (fun i =>
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := by
        ring
  have hterm1 :
      (4 / denom) * ((L / σ) * D) =
        (4 * L * D) / (σ * denom) := by
    field_simp [denom, hdenom_pos.ne']
  calc
    f (ySeq N : E) ≤
        (4 / denom) * ((L / σ) * D) +
          (4 / denom) *
            Finset.sum (Finset.range (N + 1)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := hmain'
    _ =
        (4 * L * D) / (σ * denom) +
          (2 / denom) *
            Finset.sum (Finset.range (N + 1)) (fun i =>
              ((i : ℝ) + 1) *
                (f (xSeq i) +
                  DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := by
      simp [hterm1, hsum_alpha, denom]

/-- Closed form: `∑_{i=0}^N ((i:ℝ)+1) = ((N:ℝ)+1)((N:ℝ)+2)/2`. -/
lemma sum_range_add_one_cast (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun i => ((i : ℝ) + 1)) =
      ((N : ℝ) + 1) * ((N : ℝ) + 2) / 2 := by
  classical
  have hNat :
      (Finset.sum (Finset.range (N + 1)) (fun i => i)) * 2 = (N + 1) * N := by
    simpa using (Finset.sum_range_id_mul_two (N + 1))
  have hCast := congrArg (fun t : ℕ => (t : ℝ)) hNat
  have hsum_i :
      Finset.sum (Finset.range (N + 1)) (fun i => (i : ℝ)) =
        ((N : ℝ) + 1) * (N : ℝ) / 2 := by
    refine (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2 ?_
    have :
        Finset.sum (Finset.range (N + 1)) (fun i => (i : ℝ)) * 2 =
          ((N : ℝ) + 1) * (N : ℝ) := by
      simpa [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
        add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hCast
    simpa [mul_assoc] using this
  calc
    Finset.sum (Finset.range (N + 1)) (fun i => ((i : ℝ) + 1)) =
        Finset.sum (Finset.range (N + 1)) (fun i => (i : ℝ)) +
          Finset.sum (Finset.range (N + 1)) (fun _ => (1 : ℝ)) := by
        simpa using
          (Finset.sum_add_distrib (s := Finset.range (N + 1))
            (f := fun i => (i : ℝ)) (g := fun _ => (1 : ℝ)))
    _ = ((N : ℝ) + 1) * (N : ℝ) / 2 + ((N : ℝ) + 1) := by
        simp [hsum_i]
    _ = ((N : ℝ) + 1) * ((N : ℝ) + 2) / 2 := by ring

/-- Supporting hyperplane inequality for a differentiable convex function on an open convex set. -/
lemma convex_support_grad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f : E → ℝ}
    (hQ_open : IsOpen Q) (hQ_convex : Convex ℝ Q) (hf_convex : ConvexOn ℝ Q f)
    (hf_diff : DifferentiableOn ℝ f Q) {u v : E} (hu : u ∈ Q) (hv : v ∈ Q) :
    f u ≥ f v + DualPairing ((fderiv ℝ f v).toLinearMap) (u - v) := by
  classical
  -- Reduce to a one-dimensional convex function on `[0,1]` and compare the derivative at `0`
  -- with the secant slope to `1`.
  let gAff : ℝ →ᵃ[ℝ] E := AffineMap.lineMap v u
  have hseg : Set.Icc (0 : ℝ) 1 ⊆ (fun t => gAff t) ⁻¹' Q := by
    intro t ht
    simpa [gAff] using hQ_convex.lineMap_mem hv hu ht
  have hgPre : ConvexOn ℝ ((fun t => gAff t) ⁻¹' Q) (fun t => f (gAff t)) := by
    simpa [Function.comp, gAff] using (hf_convex.comp_affineMap gAff)
  have hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (gAff t)) := by
    refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hgPre.2 (hseg hx) (hseg hy) ha hb hab
  have hvAt : DifferentiableAt ℝ f v :=
    (hf_diff v hv).differentiableAt (hQ_open.mem_nhds hv)
  have hInner : HasDerivAt (fun t : ℝ => gAff t) (u - v) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => v + t • (u - v)) (u - v) 0 := by
      simpa using
        (HasDerivAt.const_add v ((hasDerivAt_id (0 : ℝ)).smul_const (u - v)))
    simpa [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm, add_left_comm,
      add_assoc] using h0
  have hDeriv : HasDerivAt (fun t : ℝ => f (gAff t)) ((fderiv ℝ f v) (u - v)) 0 := by
    have hAff0 : gAff 0 = v := by
      simp [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have hF : HasFDerivAt f (fderiv ℝ f v) (gAff 0) := by
      simpa [hAff0] using hvAt.hasFDerivAt
    simpa [Function.comp] using
      (HasFDerivAt.comp_hasDerivAt (x := 0) (f := fun t : ℝ => gAff t) (l := f) hF hInner)
  have hle : ((fderiv ℝ f v) (u - v)) ≤ slope (fun t : ℝ => f (gAff t)) 0 1 := by
    have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have hy1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    simpa using hg.le_slope_of_hasDerivAt hx0 hy1 (by norm_num) hDeriv
  have hslope :
      slope (fun t : ℝ => f (gAff t)) 0 1 = f (gAff 1) - f (gAff 0) := by
    simp [slope_def_field]
  have hfinal : f (gAff 0) + ((fderiv ℝ f v) (u - v)) ≤ f (gAff 1) := by
    linarith [hle, hslope]
  have hAff0 : gAff 0 = v := by
    simp [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hAff1 : gAff 1 = u := by
    simp [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  -- Rewrite back in terms of `u, v`.
  simpa [DualPairing, hAff0, hAff1, add_comm, add_left_comm, add_assoc] using hfinal
