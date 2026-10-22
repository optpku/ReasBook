/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_3_1_2
public import glowinski_admm_counterexample.GlowinskiADMM.theorem_2_1_4_ADMM
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GraphNormalization
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.ReducedNormalization
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConsensusBridge
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProximalSubgradient

@[expose] public section

open scoped RealInnerProductSpace

namespace ERealConvex

/-- Translate an extended-real function to `x₀` and subtract the affine function
supported there by `p`. -/
noncomputable def centerAt {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (x₀ p : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun x ↦ φ (x₀ + x) - (φ x₀ + ((dotProduct p x : ℝ) : EReal))

/-- A finite supporting value makes the literal subtraction formula equal to
its real affine normalization. -/
private lemma centerAt_eq_normalized {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {x₀ p : Fin n → ℝ} (hp : ADMM.IsSubgradientAt φ p x₀) :
    centerAt φ x₀ p = ADMM.ConvergenceProof.normalizedObjective φ x₀ p := by
  obtain ⟨c, hc, _⟩ := hp
  funext x
  simp only [centerAt, ADMM.ConvergenceProof.normalizedObjective, hc,
    EReal.toReal_coe, ← EReal.coe_add, sub_eq_add_neg, ← EReal.coe_neg]
  congr 1
  · rw [add_comm x₀ x]
  · congr 1
    ring

/-- Evaluation formula for affine centering of an extended-real function. -/
theorem centerAt_apply {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (x₀ p x : Fin n → ℝ) :
    centerAt φ x₀ p x =
      φ (x₀ + x) - (φ x₀ + ((dotProduct p x : ℝ) : EReal)) := by
  rfl

/-- Centering at a finite supported point gives value zero at the origin. -/
theorem centerAt_zero {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {x₀ p : Fin n → ℝ} (hp : ADMM.IsSubgradientAt φ p x₀) :
    centerAt φ x₀ p 0 = 0 := by
  obtain ⟨c, hc, _⟩ := hp
  simp [centerAt, hc, ← EReal.coe_sub]

/-- Subtracting a supporting affine function makes the centered function nonnegative. -/
theorem centerAt_nonneg {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {x₀ p : Fin n → ℝ} (hp : ADMM.IsSubgradientAt φ p x₀) (x : Fin n → ℝ) :
    0 ≤ centerAt φ x₀ p x := by
  obtain ⟨c, hc, hs⟩ := hp
  unfold centerAt
  rw [hc, ← EReal.coe_add]
  apply (EReal.sub_nonneg (Or.inr (EReal.coe_ne_top _))
    (Or.inr (EReal.coe_ne_bot _))).2
  simpa only [hc, add_sub_cancel_left, ← EReal.coe_add] using hs (x₀ + x)

/-- Affine centering preserves closed proper convexity at a supported point. -/
theorem centerAt_isClosedProperConvex {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {x₀ p : Fin n → ℝ} (hφ : ADMM.IsClosedProperConvex φ)
    (hp : ADMM.IsSubgradientAt φ p x₀) :
    ADMM.IsClosedProperConvex (centerAt φ x₀ p) := by
  rw [centerAt_eq_normalized hp]
  exact ADMM.ConvergenceProof.normalizedObjective_closedProperConvex hφ hp

/-- Affine centering followed by reflection in the origin. -/
noncomputable def reflectedCenterAt {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (x₀ p : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun x ↦ centerAt φ x₀ p (-x)

/-- Evaluation formula for reflected affine centering. -/
theorem reflectedCenterAt_apply {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (x₀ p x : Fin n → ℝ) :
    reflectedCenterAt φ x₀ p x =
      φ (x₀ - x) - (φ x₀ + ((dotProduct p (-x) : ℝ) : EReal)) := by
  rfl

/-- Reflected centering has value zero at the origin. -/
theorem reflectedCenterAt_zero {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {x₀ p : Fin n → ℝ} (hp : ADMM.IsSubgradientAt φ p x₀) :
    reflectedCenterAt φ x₀ p 0 = 0 := by
  simpa only [reflectedCenterAt, neg_zero] using centerAt_zero hp

/-- Reflected centering remains nonnegative after subtracting a supporting affine function. -/
theorem reflectedCenterAt_nonneg {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {x₀ p : Fin n → ℝ} (hp : ADMM.IsSubgradientAt φ p x₀) (x : Fin n → ℝ) :
    0 ≤ reflectedCenterAt φ x₀ p x := by
  exact centerAt_nonneg hp (-x)

/-- Reflection preserves closed proper convexity of an affine-centered function. -/
theorem reflectedCenterAt_isClosedProperConvex {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} {x₀ p : Fin n → ℝ}
    (hφ : ADMM.IsClosedProperConvex φ) (hp : ADMM.IsSubgradientAt φ p x₀) :
    ADMM.IsClosedProperConvex (reflectedCenterAt φ x₀ p) := by
  exact ADMM.ConvergenceProof.reflectedObjective_closedProperConvex
    (centerAt_isClosedProperConvex hφ hp)

/-- The finite centering formula transports a supported graph point. -/
private lemma centerAt_subgradient {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    (hφ : ADMM.IsClosedProperConvex φ) {x₀ p₀ x p : Fin n → ℝ}
    (h₀ : ADMM.IsSubgradientAt φ p₀ x₀) (hx : ADMM.IsSubgradientAt φ p x) :
    ADMM.IsSubgradientAt (centerAt φ x₀ p₀) (p - p₀) (x - x₀) := by
  rw [centerAt_eq_normalized h₀]
  exact ADMM.ConvergenceProof.subgradient_normalized hφ x₀ p₀ hx

end ERealConvex

namespace ADMM.Scaled

universe u

/-- The primal residual `q k - η k` of a scaled consensus trajectory. -/
def residual {E : Type u} [AddGroup E] (q eta : ℕ → E) (k : ℕ) : E :=
  q k - eta k

/-- Evaluation formula for the scaled primal residual. -/
theorem residual_apply {E : Type u} [AddGroup E] (q eta : ℕ → E) (k : ℕ) :
    residual q eta k = q k - eta k := by
  rfl

/-- The first graph normal at the update producing step `k + 1`. -/
def firstNormal {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (q eta w : ℕ → E) (k : ℕ) : E :=
  eta k - γ • w k - q (k + 1)

/-- Evaluation formula for the first graph normal. -/
theorem firstNormal_apply {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (q eta w : ℕ → E) (k : ℕ) :
    firstNormal γ q eta w k = eta k - γ • w k - q (k + 1) := by
  rfl

/-- The second graph normal at the update producing step `k + 1`. -/
def secondNormal {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (q eta w : ℕ → E) (k : ℕ) : E :=
  γ • w k + residual q eta (k + 1)

/-- Evaluation formula for the second graph normal. -/
theorem secondNormal_apply {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (q eta w : ℕ → E) (k : ℕ) :
    secondNormal γ q eta w k = γ • w k + residual q eta (k + 1) := by
  rfl

/-- The support value of the first coordinate-space graph point at step `k + 1`. -/
def firstMargin {n : ℕ} (γ : ℝ) (q eta w : ℕ → Fin n → ℝ) (k : ℕ) : ℝ :=
  dotProduct (firstNormal γ q eta w k) (q (k + 1))

/-- Evaluation formula for the first support value. -/
theorem firstMargin_apply {n : ℕ} (γ : ℝ) (q eta w : ℕ → Fin n → ℝ) (k : ℕ) :
    firstMargin γ q eta w k = dotProduct (firstNormal γ q eta w k) (q (k + 1)) := by
  rfl

/-- The support value of the second coordinate-space graph point at step `k + 1`. -/
def secondMargin {n : ℕ} (γ : ℝ) (q eta w : ℕ → Fin n → ℝ) (k : ℕ) : ℝ :=
  dotProduct (secondNormal γ q eta w k) (eta (k + 1))

/-- Evaluation formula for the second support value. -/
theorem secondMargin_apply {n : ℕ} (γ : ℝ) (q eta w : ℕ → Fin n → ℝ) (k : ℕ) :
    secondMargin γ q eta w k =
      dotProduct (secondNormal γ q eta w k) (eta (k + 1)) := by
  rfl

end ADMM.Scaled

namespace ADMM.KKTNormalization

/-- The first reduced objective recentered at a selected reduced KKT point. -/
noncomputable def firstObjective {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (β : ℝ) (qBar uBar : Fin m → ℝ) : (Fin m → ℝ) → EReal :=
  ERealConvex.centerAt (P.reduced β).f qBar (-uBar)

/-- Evaluation formula for the normalized first objective. -/
theorem firstObjective_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (β : ℝ) (qBar uBar x : Fin m → ℝ) :
    firstObjective P β qBar uBar x =
      (P.reduced β).f (qBar + x) -
        ((P.reduced β).f qBar + ((dotProduct (-uBar) x : ℝ) : EReal)) := by
  rfl

/-- The reflected second reduced objective recentered at a selected reduced KKT point. -/
noncomputable def secondObjective {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (β : ℝ) (vBar uBar : Fin m → ℝ) : (Fin m → ℝ) → EReal :=
  ERealConvex.reflectedCenterAt (P.reduced β).g vBar (-uBar)

/-- Evaluation formula for the normalized second objective. -/
theorem secondObjective_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (β : ℝ) (vBar uBar eta : Fin m → ℝ) :
    secondObjective P β vBar uBar eta =
      (P.reduced β).g (vBar - eta) -
        ((P.reduced β).g vBar + ((dotProduct (-uBar) (-eta) : ℝ) : EReal)) := by
  rfl

/-- The first reduced image sequence translated by its KKT value. -/
def q {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (z : Trajectory P β γ) (qBar : Fin m → ℝ) : ℕ → Fin m → ℝ :=
  fun k ↦ P.A.mulVec (z.x k) - qBar

/-- Evaluation formula for the normalized first image sequence. -/
theorem q_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (z : Trajectory P β γ) (qBar : Fin m → ℝ) (k : ℕ) :
    q P β γ z qBar k = P.A.mulVec (z.x k) - qBar := by
  rfl

/-- The reflected second reduced image sequence translated by its KKT value. -/
def eta {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (z : Trajectory P β γ) (vBar : Fin m → ℝ) : ℕ → Fin m → ℝ :=
  fun k ↦ vBar - (P.B.mulVec (z.y k) - P.b)

/-- Evaluation formula for the normalized reflected second image sequence. -/
theorem eta_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (z : Trajectory P β γ) (vBar : Fin m → ℝ) (k : ℕ) :
    eta P β γ z vBar k = vBar - (P.B.mulVec (z.y k) - P.b) := by
  rfl

/-- The reduced multiplier translated by its KKT value and scaled by `γ⁻¹`. -/
noncomputable def w {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (z : Trajectory P β γ) (uBar : Fin m → ℝ) : ℕ → Fin m → ℝ :=
  fun k ↦ γ⁻¹ • (β⁻¹ • z.multiplier k - uBar)

/-- Evaluation formula for the translated and scaled multiplier sequence. -/
theorem w_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (z : Trajectory P β γ) (uBar : Fin m → ℝ) (k : ℕ) :
    w P β γ z uBar k = γ⁻¹ • (β⁻¹ • z.multiplier k - uBar) := by
  rfl

section SourceLaws

variable {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
variable (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
variable (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
variable (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ)
variable (qBar vBar uBar : Fin m → ℝ)
variable (hBar : (P.reduced β).IsKKT qBar vBar uBar)

include hf hg hKKT hβ hγ z hBar

/-- The normalized first objective vanishes at the translated KKT point. -/
theorem firstObjective_zero : firstObjective P β qBar uBar 0 = 0 := by
  have hs : IsSubgradientAt (P.reduced β).f (-uBar) qBar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hBar.firstStationary
  exact ERealConvex.centerAt_zero hs

/-- The normalized second objective vanishes at the reflected KKT point. -/
theorem secondObjective_zero : secondObjective P β vBar uBar 0 = 0 := by
  have hs : IsSubgradientAt (P.reduced β).g (-uBar) vBar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hBar.secondStationary
  exact ERealConvex.reflectedCenterAt_zero hs

/-- The normalized first objective is everywhere nonnegative. -/
theorem firstObjective_nonneg (x : Fin m → ℝ) :
    0 ≤ firstObjective P β qBar uBar x := by
  have hs : IsSubgradientAt (P.reduced β).f (-uBar) qBar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hBar.firstStationary
  exact ERealConvex.centerAt_nonneg hs x

/-- The normalized second objective is everywhere nonnegative. -/
theorem secondObjective_nonneg (eta : Fin m → ℝ) :
    0 ≤ secondObjective P β vBar uBar eta := by
  have hs : IsSubgradientAt (P.reduced β).g (-uBar) vBar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hBar.secondStationary
  exact ERealConvex.reflectedCenterAt_nonneg hs eta

/-- The normalized first objective remains closed proper convex. -/
theorem firstObjective_isClosedProperConvex :
    IsClosedProperConvex (firstObjective P β qBar uBar) := by
  have hs : IsSubgradientAt (P.reduced β).f (-uBar) qBar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hBar.firstStationary
  exact ERealConvex.centerAt_isClosedProperConvex
    (P.reducedFirst_isClosedProperConvex hf hg hKKT hβ hγ z) hs

/-- The normalized second objective remains closed proper convex. -/
theorem secondObjective_isClosedProperConvex :
    IsClosedProperConvex (secondObjective P β vBar uBar) := by
  have hs : IsSubgradientAt (P.reduced β).g (-uBar) vBar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hBar.secondStationary
  exact ERealConvex.reflectedCenterAt_isClosedProperConvex
    (P.reducedSecond_isClosedProperConvex hf hg hKKT hβ hγ z) hs

/-- Recenter the first attained reduced graph point at the chosen KKT pair. -/
private theorem firstGraph (k : ℕ) :
    IsSubgradientAt (firstObjective P β qBar uBar)
      (Scaled.firstNormal γ (q P β γ z qBar) (eta P β γ z vBar)
        (w P β γ z uBar) k) (q P β γ z qBar (k + 1)) := by
  have hfeas : qBar + vBar = 0 := by
    simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
      Matrix.one_mulVec] using hBar.feasible
  have hsStar : IsSubgradientAt (P.reduced β).f (-uBar) qBar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hBar.firstStationary
  have hs := ERealConvex.centerAt_subgradient
    (P.reducedFirst_isClosedProperConvex hf hg hKKT hβ hγ z) hsStar
    (reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z k).1
  have hnormal : Scaled.firstNormal γ (q P β γ z qBar) (eta P β γ z vBar)
      (w P β γ z uBar) k =
      (-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k -
        P.A.mulVec (z.x (k + 1))) - -uBar := by
    dsimp only [Scaled.firstNormal, q, eta, w]
    rw [smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]
    have h := eq_neg_of_add_eq_zero_right hfeas
    rw [h]
    module
  rw [hnormal]
  exact hs

/-- Reflect the second attained reduced graph point after KKT centering. -/
private theorem secondGraph (k : ℕ) :
    IsSubgradientAt (secondObjective P β vBar uBar)
      (Scaled.secondNormal γ (q P β γ z qBar) (eta P β γ z vBar)
        (w P β γ z uBar) k) (eta P β γ z vBar (k + 1)) := by
  have hfeas : qBar + vBar = 0 := by
    simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
      Matrix.one_mulVec] using hBar.feasible
  have hsStar : IsSubgradientAt (P.reduced β).g (-uBar) vBar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hBar.secondStationary
  have hs := ConvergenceProof.subgradient_reflected
    (ERealConvex.centerAt_subgradient
      (P.reducedSecond_isClosedProperConvex hf hg hKKT hβ hγ z) hsStar
      (reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z k).2)
  have hnormal : Scaled.secondNormal γ (q P β γ z qBar) (eta P β γ z vBar)
      (w P β γ z uBar) k =
      -((-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k -
        (P.B.mulVec (z.y (k + 1)) - P.b)) - -uBar) := by
    dsimp only [Scaled.secondNormal, Scaled.residual, q, eta, w]
    rw [smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]
    have h := eq_neg_of_add_eq_zero_right hfeas
    rw [h]
    module
  have heta : eta P β γ z vBar (k + 1) =
      -(P.B.mulVec (z.y (k + 1)) - P.b - vBar) := by
    dsimp only [eta]
    module
  rw [hnormal, heta]
  exact hs

/-- The translated first image is the proximal point produced at step `k + 1`. -/
theorem firstProx (k : ℕ) :
    IsProxPoint (firstObjective P β qBar uBar)
      (eta P β γ z vBar k - γ • w P β γ z uBar k)
      (q P β γ z qBar (k + 1)) := by
  exact isProxPoint_of_subgradient (firstGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k)

/-- The reflected second image is the proximal point produced at step `k + 1`. -/
theorem secondProx (k : ℕ) :
    IsProxPoint (secondObjective P β vBar uBar)
      (q P β γ z qBar (k + 1) + γ • w P β γ z uBar k)
      (eta P β γ z vBar (k + 1)) := by
  apply isProxPoint_of_subgradient
  have hnormal : (q P β γ z qBar (k + 1) + γ • w P β γ z uBar k) -
      eta P β γ z vBar (k + 1) =
      Scaled.secondNormal γ (q P β γ z qBar) (eta P β γ z vBar)
        (w P β γ z uBar) k := by
    dsimp only [Scaled.secondNormal, Scaled.residual]
    module
  rw [hnormal]
  exact secondGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k

/-- The translated scaled multiplier advances by the new primal residual. -/
theorem w_succ (k : ℕ) :
    w P β γ z uBar (k + 1) = w P β γ z uBar k +
      Scaled.residual (q P β γ z qBar) (eta P β γ z vBar) (k + 1) := by
  have hfeas : qBar + vBar = 0 := by
    simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
      Matrix.one_mulVec] using hBar.feasible
  have hrec := Trajectory.scaledMultiplier_imageUpdate P hf hg hKKT hβ hγ z
  have hdiff := ConvergenceProof.scaled_multiplier_difference hγ.ne'
    (fun k ↦ P.A.mulVec (z.x k)) (fun k ↦ P.B.mulVec (z.y k) - P.b)
    (fun k ↦ β⁻¹ • z.multiplier k) uBar hrec k
  have hres : Scaled.residual (q P β γ z qBar) (eta P β γ z vBar) (k + 1) =
      P.A.mulVec (z.x (k + 1)) + (P.B.mulVec (z.y (k + 1)) - P.b) := by
    dsimp only [Scaled.residual, q, eta]
    have h := eq_neg_of_add_eq_zero_right hfeas
    rw [h]
    module
  have hd : w P β γ z uBar (k + 1) - w P β γ z uBar k =
      Scaled.residual (q P β γ z qBar) (eta P β γ z vBar) (k + 1) := by
    rw [hres]
    exact hdiff
  calc
    w P β γ z uBar (k + 1) =
        (w P β γ z uBar (k + 1) - w P β γ z uBar k) + w P β γ z uBar k := by
          rw [sub_add_cancel]
    _ = _ := by rw [hd, add_comm]

/-- The first graph normal is a subgradient of the normalized first objective. -/
theorem firstNormal_subgradient (k : ℕ) :
    IsSubgradientAt (firstObjective P β qBar uBar)
      (Scaled.firstNormal γ (q P β γ z qBar) (eta P β γ z vBar)
        (w P β γ z uBar) k)
      (q P β γ z qBar (k + 1)) := by
  exact firstGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k

/-- The second graph normal is a subgradient of the normalized second objective. -/
theorem secondNormal_subgradient (k : ℕ) :
    IsSubgradientAt (secondObjective P β vBar uBar)
      (Scaled.secondNormal γ (q P β γ z qBar) (eta P β γ z vBar)
        (w P β γ z uBar) k)
      (eta P β γ z vBar (k + 1)) := by
  exact secondGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k

/-- The normalized first objective value lies between zero and its support value. -/
theorem firstMargin_bounds (k : ℕ) :
    0 ≤ firstObjective P β qBar uBar (q P β γ z qBar (k + 1)) ∧
      firstObjective P β qBar uBar (q P β γ z qBar (k + 1)) ≤
        (Scaled.firstMargin γ (q P β γ z qBar) (eta P β γ z vBar)
          (w P β γ z uBar) k) := by
  obtain ⟨c, hc, hs⟩ := firstGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k
  have hzero := firstObjective_zero P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar
  have hsupport := hs 0
  simp only [hzero, hc, zero_sub, dotProduct_neg, ← EReal.coe_add,
    ← EReal.coe_zero, EReal.coe_le_coe_iff] at hsupport
  constructor
  · exact firstObjective_nonneg P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar (q P β γ z qBar (k + 1))
  · change (firstObjective P β qBar uBar) (q P β γ z qBar (k + 1)) ≤ _
    rw [hc]
    apply EReal.coe_le_coe_iff.mpr
    dsimp only [Scaled.firstMargin]
    linarith

/-- The normalized second objective value lies between zero and its support value. -/
theorem secondMargin_bounds (k : ℕ) :
    0 ≤ secondObjective P β vBar uBar (eta P β γ z vBar (k + 1)) ∧
      secondObjective P β vBar uBar (eta P β γ z vBar (k + 1)) ≤
        (Scaled.secondMargin γ (q P β γ z qBar) (eta P β γ z vBar)
          (w P β γ z uBar) k) := by
  obtain ⟨c, hc, hs⟩ := secondGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k
  have hzero := secondObjective_zero P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar
  have hsupport := hs 0
  simp only [hzero, hc, zero_sub, dotProduct_neg, ← EReal.coe_add,
    ← EReal.coe_zero, EReal.coe_le_coe_iff] at hsupport
  constructor
  · exact secondObjective_nonneg P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar (eta P β γ z vBar (k + 1))
  · change (secondObjective P β vBar uBar) (eta P β γ z vBar (k + 1)) ≤ _
    rw [hc]
    apply EReal.coe_le_coe_iff.mpr
    dsimp only [Scaled.secondMargin]
    linarith

/-- The explicit normalization is a consensus ADMM trajectory with dual sequence `γ • w`. -/
theorem isTrajectory :
    ConsensusADMM.IsTrajectory γ
      (fun x : EuclideanSpace ℝ (Fin m) ↦
        firstObjective P β qBar uBar (WithLp.ofLp x))
      (fun x : EuclideanSpace ℝ (Fin m) ↦
        secondObjective P β vBar uBar (WithLp.ofLp x))
      (fun k ↦ WithLp.toLp 2 (q P β γ z qBar k))
      (fun k ↦ WithLp.toLp 2 (eta P β γ z vBar k))
      (fun k ↦ WithLp.toLp 2 (γ • w P β γ z uBar k)) := by
  intro k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [← real_inner_self_eq_norm_sq,
      ConsensusADMM.CoordinateBridge.inner_eq_dot, WithLp.ofLp_sub,
      WithLp.ofLp_toLp] using
      first_augmented_minimum_of_prox
        (firstProx P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k) x.ofLp
  · intro x
    simpa only [← real_inner_self_eq_norm_sq,
      ConsensusADMM.CoordinateBridge.inner_eq_dot, WithLp.ofLp_sub,
      WithLp.ofLp_toLp] using
      second_augmented_minimum_of_prox
        (secondProx P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k) x.ofLp
  · change firstObjective P β qBar uBar (q P β γ z qBar (k + 1)) ≠ ⊤
    obtain ⟨c, hc, _⟩ := firstGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k
    rw [hc]
    exact EReal.coe_ne_top c
  · change secondObjective P β vBar uBar (eta P β γ z vBar (k + 1)) ≠ ⊤
    obtain ⟨c, hc, _⟩ := secondGraph P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k
    rw [hc]
    exact EReal.coe_ne_top c
  · simpa only [Scaled.residual, smul_add, WithLp.toLp_add,
      WithLp.toLp_smul, WithLp.toLp_sub] using
      congrArg (fun t : Fin m → ℝ ↦ WithLp.toLp 2 (γ • t))
        (w_succ P hf hg hKKT β γ hβ hγ z qBar vBar uBar hBar k)

end SourceLaws

end ADMM.KKTNormalization
