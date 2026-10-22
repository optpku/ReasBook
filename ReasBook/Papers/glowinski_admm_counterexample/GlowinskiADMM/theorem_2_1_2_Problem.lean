/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConvexFunction
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Optimality

@[expose] public section

universe u

/- Compatibility checks for the shared closed-proper-convex API. -/
#check (ADMM.IsClosedProperConvex :
  {X : Type u} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → (X → EReal) → Prop)

#check (ADMM.IsClosedProperConvex.ofEpigraph :
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → EReal},
    Convex ℝ {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} →
    IsClosed {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} →
    (∀ x, f x ≠ ⊥) → (∃ x, f x ≠ ⊤) → ADMM.IsClosedProperConvex f)

#check (ADMM.IsClosedProperConvex.spec :
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → EReal},
    ADMM.IsClosedProperConvex f →
    Convex ℝ {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} ∧
      IsClosed {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} ∧
      (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤)

/- Compatibility checks for the shared optimal-multiplier API. -/
#check (ADMM.Problem.IsOptimalMultiplier :
  ∀ {n₁ n₂ m : ℕ}, ADMM.Problem n₁ n₂ m → (Fin m → ℝ) → Prop)

#check (ADMM.Problem.isOptimalMultiplier_iff :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m) (multiplier : Fin m → ℝ),
    P.IsOptimalMultiplier multiplier ↔ ∃ x y, P.IsKKT x y multiplier)
