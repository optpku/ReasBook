module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ImageReduction

@[expose] public section

/- Lemma 3.1.2 (1): the first reduced objective is closed proper convex. -/
#check (ADMM.Problem.reducedFirst_isClosedProperConvex :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ → ADMM.Trajectory P β γ →
      ADMM.IsClosedProperConvex (P.reduced β).f)

/- Lemma 3.1.2 (2): the second reduced objective is closed proper convex. -/
#check (ADMM.Problem.reducedSecond_isClosedProperConvex :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ → ADMM.Trajectory P β γ →
      ADMM.IsClosedProperConvex (P.reduced β).g)

/- Lemma 3.1.2 (3): the reduced problem has a KKT triple. -/
#check (ADMM.Problem.reduced_exists_kkt :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ → ADMM.Trajectory P β γ →
      ∃ q v u, (P.reduced β).IsKKT q v u)

/- Lemma 3.1.2 (4): the reduced optimal value is the original value divided by `β`. -/
#check (ADMM.Problem.reduced_optimalValue :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ → ADMM.Trajectory P β γ →
      (P.reduced β).optimalValue = P.optimalValue / (β : EReal))

/- Lemma 3.1.2 (5): first-block image values agree through biconjugation. -/
#check (ADMM.Trajectory.firstImage_values :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ →
      ∀ (z : ADMM.Trajectory P β γ) (k : ℕ),
        ADMM.ImageReduction.fiberInf P.f P.A (P.A.mulVec (z.x (k + 1))) =
            ERealConvex.fenchelBiconjugate
              (ADMM.ImageReduction.fiberInf P.f P.A)
              (P.A.mulVec (z.x (k + 1))) ∧
          ERealConvex.fenchelBiconjugate
              (ADMM.ImageReduction.fiberInf P.f P.A)
              (P.A.mulVec (z.x (k + 1))) = P.f (z.x (k + 1)))

/- Lemma 3.1.2 (6): second-block image values agree through biconjugation. -/
#check (ADMM.Trajectory.secondImage_values :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ →
      ∀ (z : ADMM.Trajectory P β γ) (k : ℕ),
        ADMM.ImageReduction.shiftedFiberInf P.g P.B P.b
            (P.B.mulVec (z.y (k + 1)) - P.b) =
            ERealConvex.fenchelBiconjugate
              (ADMM.ImageReduction.shiftedFiberInf P.g P.B P.b)
              (P.B.mulVec (z.y (k + 1)) - P.b) ∧
          ERealConvex.fenchelBiconjugate
              (ADMM.ImageReduction.shiftedFiberInf P.g P.B P.b)
              (P.B.mulVec (z.y (k + 1)) - P.b) = P.g (z.y (k + 1)))

/- Lemma 3.1.2 (7): the first image update is a relational proximal point. -/
#check (ADMM.Trajectory.firstImage_isProxPoint :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ →
      ∀ (z : ADMM.Trajectory P β γ) (k : ℕ),
        ADMM.IsProxPoint (P.reduced β).f
          (-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k)
          (P.A.mulVec (z.x (k + 1))))

/- Lemma 3.1.2 (8): the second image update is a relational proximal point. -/
#check (ADMM.Trajectory.secondImage_isProxPoint :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ →
      ∀ (z : ADMM.Trajectory P β γ) (k : ℕ),
        ADMM.IsProxPoint (P.reduced β).g
          (-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k)
          (P.B.mulVec (z.y (k + 1)) - P.b))

/- Lemma 3.1.2 (9): the scaled multiplier obeys the image-update recurrence. -/
#check (ADMM.Trajectory.scaledMultiplier_imageUpdate :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ {β γ : ℝ}, 0 < β → 0 < γ →
      ∀ (z : ADMM.Trajectory P β γ) (k : ℕ),
        β⁻¹ • z.multiplier (k + 1) = β⁻¹ • z.multiplier k +
          γ • (P.A.mulVec (z.x (k + 1)) +
            (P.B.mulVec (z.y (k + 1)) - P.b)))
