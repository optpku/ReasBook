module

import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform

/- Infrastructure I.8a (Algebra and composition of finite uniform jets) (1):
uniform finite jets are closed under addition. -/
#check (FiniteTaylorJet.IsUniformOn.add :
  ∀ {Θ : Type*} {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {f g : Θ → E → F}
    {P Q : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ},
    FiniteTaylorJet.IsUniformOn f P a K →
      FiniteTaylorJet.IsUniformOn g Q a K →
        FiniteTaylorJet.IsUniformOn (fun θ z ↦ f θ z + g θ z)
          (fun θ ↦ FiniteTaylorJet.add (P θ) (Q θ)) a K)

/- Infrastructure I.8a (Algebra and composition of finite uniform jets) (2):
uniform finite jets valued in a normed real algebra are closed under
multiplication. -/
#check (FiniteTaylorJet.IsUniformOn.mul :
  ∀ {Θ : Type*} {E : Type*} {A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {m : ℕ} {f g : Θ → E → A}
    {P Q : Θ → FiniteTaylorJet ℝ E A m} {a : E} {K : Set Θ},
    FiniteTaylorJet.IsUniformOn f P a K →
      FiniteTaylorJet.IsUniformOn g Q a K →
        FiniteTaylorJet.IsUniformOn (fun θ z ↦ f θ z * g θ z)
          (fun θ ↦ FiniteTaylorJet.mul (P θ) (Q θ)) a K)

/- Infrastructure I.8a (Algebra and composition of finite uniform jets) (3):
inversion preserves real uniform finite jets at a common nonzero base value. -/
#check (FiniteTaylorJet.IsUniformOn.inv :
  ∀ {Θ : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {f : Θ → E → ℝ}
    {P : Θ → FiniteTaylorJet ℝ E ℝ m} {a : E} {K : Set Θ} (c : ℝ),
    FiniteTaylorJet.IsUniformOn f P a K →
      (∀ θ ∈ K, (P θ).constantCoeff = c) → c ≠ 0 →
        FiniteTaylorJet.IsUniformOn (fun θ z ↦ (f θ z)⁻¹)
          (fun θ ↦ FiniteTaylorJet.inv (P θ)) a K)

/- Infrastructure I.8a (Algebra and composition of finite uniform jets) (4):
square root preserves real uniform finite jets at a common positive base value. -/
#check (FiniteTaylorJet.IsUniformOn.sqrt :
  ∀ {Θ : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {f : Θ → E → ℝ}
    {P : Θ → FiniteTaylorJet ℝ E ℝ m} {a : E} {K : Set Θ} (c : ℝ),
    FiniteTaylorJet.IsUniformOn f P a K →
      (∀ θ ∈ K, (P θ).constantCoeff = c) → 0 < c →
        FiniteTaylorJet.IsUniformOn (fun θ z ↦ Real.sqrt (f θ z))
          (fun θ ↦ FiniteTaylorJet.sqrt (P θ)) a K)

/- Infrastructure I.8a (Algebra and composition of finite uniform jets) (5):
the norm preserves uniform finite jets away from the zero base vector. -/
#check (FiniteTaylorJet.IsUniformOn.norm :
  ∀ {Θ : Type*} {E : Type*} {H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {m : ℕ} {f : Θ → E → H}
    {P : Θ → FiniteTaylorJet ℝ E H m} {a : E} {K : Set Θ} (c : H),
    FiniteTaylorJet.IsUniformOn f P a K →
      (∀ θ ∈ K, (P θ).constantCoeff = c) → c ≠ 0 →
        FiniteTaylorJet.IsUniformOn (fun θ z ↦ ‖f θ z‖)
          (fun θ ↦ FiniteTaylorJet.norm (P θ)) a K)

/- Infrastructure I.8a (Algebra and composition of finite uniform jets) (6):
uniform finite jets compose when their expansion bases match. -/
#check (FiniteTaylorJet.IsUniformOn.comp :
  ∀ {Θ : Type*} {E : Type*} {F : Type*} {G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} {f : Θ → E → F} {g : Θ → F → G}
    {P : Θ → FiniteTaylorJet ℝ E F m}
    {Q : Θ → FiniteTaylorJet ℝ F G m} {a : E} {b : F} {K : Set Θ},
    FiniteTaylorJet.IsUniformOn f P a K →
      FiniteTaylorJet.IsUniformOn g Q b K →
        (∀ θ ∈ K, f θ a = b) →
          FiniteTaylorJet.IsUniformOn (fun θ z ↦ g θ (f θ z))
            (fun θ ↦ FiniteTaylorJet.comp (Q θ) (P θ)) a K)

/- Infrastructure I.8a (Algebra and composition of finite uniform jets) (7):
uniform two-variable jets specialize along the path `ε ↦ (ε, ε ^ 2)`. -/
#check (FiniteTaylorJet.IsUniformOn.weightedPath :
  ∀ {Θ : Type*} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {f : Θ → (ℝ × ℝ) → F}
    {J : Θ → FiniteTaylorJet ℝ (ℝ × ℝ) F m} {K : Set Θ},
    FiniteTaylorJet.IsUniformOn f J (0, 0) K →
      FiniteTaylorJet.IsUniformOn (fun θ ε ↦ f θ (ε, ε ^ 2))
        (fun θ ↦ FiniteTaylorJet.comp (J θ) (FiniteTaylorJet.weightedPathJet m)) 0 K)
