module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Algebra
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Matrix
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Reparameterization
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Sqrt

open Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology

universe u v w

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (1):
addition of uniform remainder estimates. -/
#check (Asymptotics.IsUniformRemainderOn.add :
  ∀ {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R S : Θ → ℝ → E} {s : Set Θ} {C D q : ℝ},
    Asymptotics.IsUniformRemainderOn R s C q →
      Asymptotics.IsUniformRemainderOn S s D q →
      Asymptotics.IsUniformRemainderOn (fun θ ε ↦ R θ ε + S θ ε) s (C + D) q)

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (2):
subtraction of uniform remainder estimates. -/
#check (Asymptotics.IsUniformRemainderOn.sub :
  ∀ {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R S : Θ → ℝ → E} {s : Set Θ} {C D q : ℝ},
    Asymptotics.IsUniformRemainderOn R s C q →
      Asymptotics.IsUniformRemainderOn S s D q →
      Asymptotics.IsUniformRemainderOn (fun θ ε ↦ R θ ε - S θ ε) s (C + D) q)

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (3):
fixed and parameter-dependent scalar multiplication of uniform remainder estimates. -/
#check (Asymptotics.IsUniformRemainderOn.const_smul :
  ∀ {Θ : Type u} {𝕜 : Type v} {E : Type w} [SeminormedRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {R : Θ → ℝ → E} {s : Set Θ} {C q : ℝ} (a : 𝕜),
    Asymptotics.IsUniformRemainderOn R s C q →
      Asymptotics.IsUniformRemainderOn (fun θ ε ↦ a • R θ ε) s (‖a‖ * C) q)
#check (Asymptotics.IsUniformRemainderOn.smul :
  ∀ {Θ : Type u} {𝕜 : Type v} {E : Type w} [SeminormedRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {a : Θ → ℝ → 𝕜} {R : Θ → ℝ → E} {s : Set Θ} {C D p q : ℝ},
    Asymptotics.IsUniformRemainderOn a s C p →
      Asymptotics.IsUniformRemainderOn R s D q → 0 ≤ C → 0 ≤ D → 0 ≤ p → 0 ≤ q →
      Asymptotics.IsUniformRemainderOn
        (fun θ ε ↦ a θ ε • R θ ε) s (C * D) (p + q))

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (4):
rectangular matrix multiplication with the Euclidean `L2Operator` norm. -/
#check (Asymptotics.IsUniformRemainderOn.matrixMul :
  ∀ {Θ : Type u} {𝕜 : Type v} [RCLike 𝕜] {m n l : ℕ}
    {R : Θ → ℝ → Matrix (Fin m) (Fin n) 𝕜}
    {S : Θ → ℝ → Matrix (Fin n) (Fin l) 𝕜} {s : Set Θ} {C D p q : ℝ},
    Asymptotics.IsUniformRemainderOn R s C p →
      Asymptotics.IsUniformRemainderOn S s D q → 0 ≤ C → 0 ≤ D → 0 ≤ p → 0 ≤ q →
      Asymptotics.IsUniformRemainderOn
        (fun θ ε ↦ R θ ε * S θ ε) s (C * D) (p + q))

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (5):
norms of uniform remainder estimates. -/
#check (Asymptotics.IsUniformRemainderOn.norm :
  ∀ {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Θ → ℝ → E} {s : Set Θ} {C q : ℝ},
    Asymptotics.IsUniformRemainderOn R s C q →
      Asymptotics.IsUniformRemainderOn (fun θ ε ↦ ‖R θ ε‖) s C q)

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (6):
binary and finite products of uniform remainder estimates. -/
#check (Asymptotics.IsUniformRemainderOn.mul :
  ∀ {Θ : Type u} {A : Type v} [SeminormedRing A] {R S : Θ → ℝ → A}
    {s : Set Θ} {C D p q : ℝ},
    Asymptotics.IsUniformRemainderOn R s C p →
      Asymptotics.IsUniformRemainderOn S s D q → 0 ≤ C → 0 ≤ D → 0 ≤ p → 0 ≤ q →
      Asymptotics.IsUniformRemainderOn
        (fun θ ε ↦ R θ ε * S θ ε) s (C * D) (p + q))
#check (Asymptotics.IsUniformRemainderOn.finsetProd :
  ∀ {Θ : Type u} {ι : Type v} {A : Type w} [SeminormedCommRing A]
    [NormOneClass A]
    (t : Finset ι) {R : ι → Θ → ℝ → A} {s : Set Θ} {C q : ι → ℝ},
    (∀ i ∈ t, Asymptotics.IsUniformRemainderOn (R i) s (C i) (q i)) →
      (∀ i ∈ t, 0 ≤ C i) → (∀ i ∈ t, 0 ≤ q i) →
      Asymptotics.IsUniformRemainderOn (fun θ ε ↦ ∏ i ∈ t, R i θ ε) s
        (∏ i ∈ t, C i) (∑ i ∈ t, q i))

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (7):
division by a factor with a uniform eventual positive norm lower bound. -/
#check (Asymptotics.IsUniformRemainderOn.div :
  ∀ {Θ : Type u} {𝕜 : Type v} [NormedDivisionRing 𝕜]
    {R D : Θ → ℝ → 𝕜} {s : Set Θ} {C q m : ℝ},
    Asymptotics.IsUniformRemainderOn R s C q → 0 < m →
      (∀ᶠ z in principal s ×ˢ 𝓝 0, m ≤ ‖D z.1 z.2‖) →
      Asymptotics.IsUniformRemainderOn (fun θ ε ↦ R θ ε / D θ ε) s (C / m) q)

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (8):
composition with a filter-tending reparameterization and a controlled transformed gauge. -/
#check (Asymptotics.IsUniformRemainderOn.comp_tendsto :
  ∀ {Θ : Type u} {Ξ : Type v} {E : Type w} [Norm E]
    {R : Θ → ℝ → E} {s : Set Θ} {t : Set Ξ} {C A q p : ℝ}
    (k : Ξ × ℝ → Θ × ℝ),
    Asymptotics.IsUniformRemainderOn R s C q →
      Tendsto k (principal t ×ˢ 𝓝 0) (principal s ×ˢ 𝓝 0) →
      Asymptotics.IsUniformRemainderOn (fun ξ ε ↦ |(k (ξ, ε)).2| ^ q) t A p →
      0 ≤ C → Asymptotics.IsUniformRemainderOn
        (fun ξ ε ↦ R (k (ξ, ε)).1 (k (ξ, ε)).2) t (C * A) p)

/- Infrastructure I.6 (Algebra of uniform parameterized remainders) (9):
square roots around a positive real base. -/
#check (Asymptotics.IsUniformRemainderOn.sqrt :
  ∀ {Θ : Type u} {R : Θ → ℝ → ℝ} {s : Set Θ} {a C q : ℝ},
    Asymptotics.IsUniformRemainderOn R s C q → 0 < a → 0 ≤ C → 0 < q →
      Asymptotics.IsUniformRemainderOn
        (fun θ ε ↦ √(a + R θ ε) - √a) s (C / √a) q)
