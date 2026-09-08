module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

public section

namespace FiniteTaylorJet

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): the iterated derivative
of a composite is the Faa di Bruno Taylor composition of the two derivative series. -/
theorem iteratedFDeriv_comp_eq_taylorComp
    {m n : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x))
    (hn : n ≤ m) :
    iteratedFDeriv ℝ n (g ∘ f) x =
      (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) n := by
  have hnm : (n : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hn
  exact iteratedFDeriv_comp hg hf hnm

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): a derivative-constructed
jet coefficient of a composite is the factorial-normalized Faa di Bruno coefficient. -/
theorem ofFunction_coeff_comp_eq_taylorComp
    {m n : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x))
    (hn : n ≤ m) :
    (ofFunction ℝ m (g ∘ f) x).coeff ⟨n, Nat.lt_succ_iff.mpr hn⟩ =
      ((n.factorial : ℝ)⁻¹) •
        (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) n := by
  rw [coeff_ofFunction]
  exact congrArg (fun T ↦ ((n.factorial : ℝ)⁻¹) • T)
    (iteratedFDeriv_comp_eq_taylorComp hf hg hn)

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): the normalized
Faa di Bruno series truncated at order `m`. -/
noncomputable def normalizedTaylorCompJet
    (m : ℕ) (f : E → F) (g : F → G) (x : E) : FiniteTaylorJet ℝ E G m :=
  { coeff := fun n ↦
      ((n : ℕ).factorial : ℝ)⁻¹ •
        (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) (n : ℕ) }

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): under finite
smoothness, the derivative-constructed composite jet is the normalized Faa di Bruno jet. -/
theorem ofFunction_comp_eq_normalizedTaylorCompJet
    {m : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x)) :
    ofFunction ℝ m (g ∘ f) x = normalizedTaylorCompJet m f g x := by
  apply ext_coeff
  intro n
  exact ofFunction_coeff_comp_eq_taylorComp hf hg (Nat.lt_succ_iff.mp n.isLt)

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): a secant of
derivative-constructed composite coefficients is the factorial-normalized secant of the
corresponding Faa di Bruno Taylor compositions. -/
theorem ofFunction_composite_coeff_sub_eq_taylorComp_sub
    {m n : ℕ} {f₁ f₂ : E → F} {g₁ g₂ : F → G} {x : E}
    (hf₁ : ContDiffAt ℝ m f₁ x) (hf₂ : ContDiffAt ℝ m f₂ x)
    (hg₁ : ContDiffAt ℝ m g₁ (f₁ x)) (hg₂ : ContDiffAt ℝ m g₂ (f₂ x))
    (hn : n ≤ m) :
    (ofFunction ℝ m (g₁ ∘ f₁) x).coeff ⟨n, Nat.lt_succ_iff.mpr hn⟩ -
        (ofFunction ℝ m (g₂ ∘ f₂) x).coeff ⟨n, Nat.lt_succ_iff.mpr hn⟩ =
      ((n.factorial : ℝ)⁻¹) •
        ((ftaylorSeries ℝ g₁ (f₁ x)).taylorComp
            (ftaylorSeries ℝ f₁ x) n -
          (ftaylorSeries ℝ g₂ (f₂ x)).taylorComp
            (ftaylorSeries ℝ f₂ x) n) := by
  rw [ofFunction_coeff_comp_eq_taylorComp hf₁ hg₁ hn,
    ofFunction_coeff_comp_eq_taylorComp hf₂ hg₂ hn, smul_sub]

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): a composite secant
coefficient splits into an inner-map variation followed by an outer-map variation at the
Faa di Bruno Taylor-series level. -/
theorem ofFunction_composite_coeff_sub_decompose
    {m n : ℕ} {f₁ f₂ : E → F} {g₁ g₂ : F → G} {x : E}
    (hf₁ : ContDiffAt ℝ m f₁ x) (hf₂ : ContDiffAt ℝ m f₂ x)
    (hg₁ : ContDiffAt ℝ m g₁ (f₁ x)) (hg₂ : ContDiffAt ℝ m g₂ (f₂ x))
    (hn : n ≤ m) :
    (ofFunction ℝ m (g₁ ∘ f₁) x).coeff ⟨n, Nat.lt_succ_iff.mpr hn⟩ -
        (ofFunction ℝ m (g₂ ∘ f₂) x).coeff ⟨n, Nat.lt_succ_iff.mpr hn⟩ =
      ((n.factorial : ℝ)⁻¹) •
        (((ftaylorSeries ℝ g₁ (f₁ x)).taylorComp
              (ftaylorSeries ℝ f₁ x) n -
            (ftaylorSeries ℝ g₁ (f₂ x)).taylorComp
              (ftaylorSeries ℝ f₂ x) n) +
          ((ftaylorSeries ℝ g₁ (f₂ x)).taylorComp
              (ftaylorSeries ℝ f₂ x) n -
            (ftaylorSeries ℝ g₂ (f₂ x)).taylorComp
              (ftaylorSeries ℝ f₂ x) n)) := by
  rw [ofFunction_coeff_comp_eq_taylorComp hf₁ hg₁ hn,
    ofFunction_coeff_comp_eq_taylorComp hf₂ hg₂ hn, smul_add]
  simp only [smul_sub]
  abel

end FiniteTaylorJet
