module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations

public section

/-!
# Finite Taylor jets of elementary function operations

This file connects the algebraic operations on `FiniteTaylorJet` with jets obtained from
functions.  The zero-jet corollaries are convenient for combining independently proved
componentwise remainder estimates.
-/

universe u v w x

namespace FiniteTaylorJet

variable {𝕜 : Type u} {E : Type v} {F : Type w} {G : Type x}
variable [NontriviallyNormedField 𝕜] [CharZero 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The finite jet of a product-valued function is the product of its component jets. -/
theorem ofFunction_prodMk {m : ℕ} {f : E → F} {g : E → G} {a : E}
    (hf : ContDiffAt 𝕜 m f a) (hg : ContDiffAt 𝕜 m g a) :
    ofFunction 𝕜 m (fun x => (f x, g x)) a =
      prod (ofFunction 𝕜 m f a) (ofFunction 𝕜 m g a) := by
  apply ext_coeff
  intro n
  rw [coeff_ofFunction, coeff_prod, coeff_ofFunction, coeff_ofFunction]
  have hn : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have horder : (n : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hn
  rw [iteratedFDeriv_prodMk hf hg horder]
  ext v
  · simp
  · simp

/-- Equal jets have a difference whose finite jet is the zero jet. -/
theorem ofFunction_sub_eq_zero_of_eq {m : ℕ} {f g : 𝕜 → F} {a : 𝕜}
    (hf : ContDiffAt 𝕜 m f a) (hg : ContDiffAt 𝕜 m g a)
    (hjet : ofFunction 𝕜 m f a = ofFunction 𝕜 m g a) :
    ofFunction 𝕜 m (fun x => f x - g x) a =
      ofFunction 𝕜 m (fun _ => (0 : F)) a := by
  rw [ofFunction_eq_zeroFunction_iff]
  intro n
  have hn : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have horder : (n : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hn
  have hder :=
    (ofFunction_eq_iff_iteratedDeriv_eq m f g a a).mp hjet n
  calc
    iteratedDeriv (n : ℕ) (fun x => f x - g x) a =
        iteratedDeriv (n : ℕ) f a - iteratedDeriv (n : ℕ) g a := by
      have hfun : (fun x => f x - g x) = f - g := by
        funext x
        rfl
      rw [hfun]
      exact iteratedDeriv_sub
        (hf.of_le horder) (hg.of_le horder)
    _ = 0 := sub_eq_zero.mpr hder

/-- A product of two functions with zero finite jets again has zero finite jet. -/
theorem ofFunction_prodMk_eq_zero {m : ℕ} {f : E → F} {g : E → G} {a : E}
    (hf : ContDiffAt 𝕜 m f a) (hg : ContDiffAt 𝕜 m g a)
    (hf0 : ofFunction 𝕜 m f a = ofFunction 𝕜 m (fun _ => (0 : F)) a)
    (hg0 : ofFunction 𝕜 m g a = ofFunction 𝕜 m (fun _ => (0 : G)) a) :
    ofFunction 𝕜 m (fun x => (f x, g x)) a =
      ofFunction 𝕜 m (fun _ => ((0, 0) : F × G)) a := by
  rw [ofFunction_prodMk hf hg, hf0, hg0]
  rw [← ofFunction_prodMk (m := m)
    (f := fun _ : E => (0 : F)) (g := fun _ : E => (0 : G))
    contDiffAt_const contDiffAt_const]

/-- Equality of two pairs of one-variable jets is preserved by pointwise addition. -/
theorem ofFunction_add_congr {m : ℕ} {f₁ f₂ g₁ g₂ : 𝕜 → F} {a : 𝕜}
    (hf₁ : ContDiffAt 𝕜 m f₁ a) (hf₂ : ContDiffAt 𝕜 m f₂ a)
    (hg₁ : ContDiffAt 𝕜 m g₁ a) (hg₂ : ContDiffAt 𝕜 m g₂ a)
    (hf : ofFunction 𝕜 m f₁ a = ofFunction 𝕜 m f₂ a)
    (hg : ofFunction 𝕜 m g₁ a = ofFunction 𝕜 m g₂ a) :
    ofFunction 𝕜 m (fun x => f₁ x + g₁ x) a =
      ofFunction 𝕜 m (fun x => f₂ x + g₂ x) a := by
  rw [ofFunction_eq_iff_iteratedDeriv_eq]
  intro n
  have hn : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have horder : (n : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hn
  have hfder := (ofFunction_eq_iff_iteratedDeriv_eq m f₁ f₂ a a).mp hf n
  have hgder := (ofFunction_eq_iff_iteratedDeriv_eq m g₁ g₂ a a).mp hg n
  change iteratedDeriv (n : ℕ) (f₁ + g₁) a =
    iteratedDeriv (n : ℕ) (f₂ + g₂) a
  rw [iteratedDeriv_add (hf₁.of_le horder)
      (hg₁.of_le horder),
    iteratedDeriv_add (hf₂.of_le horder)
      (hg₂.of_le horder), hfder, hgder]

/-- Equality of two pairs of one-variable jets is preserved by pointwise subtraction. -/
theorem ofFunction_sub_congr {m : ℕ} {f₁ f₂ g₁ g₂ : 𝕜 → F} {a : 𝕜}
    (hf₁ : ContDiffAt 𝕜 m f₁ a) (hf₂ : ContDiffAt 𝕜 m f₂ a)
    (hg₁ : ContDiffAt 𝕜 m g₁ a) (hg₂ : ContDiffAt 𝕜 m g₂ a)
    (hf : ofFunction 𝕜 m f₁ a = ofFunction 𝕜 m f₂ a)
    (hg : ofFunction 𝕜 m g₁ a = ofFunction 𝕜 m g₂ a) :
    ofFunction 𝕜 m (fun x => f₁ x - g₁ x) a =
      ofFunction 𝕜 m (fun x => f₂ x - g₂ x) a := by
  rw [ofFunction_eq_iff_iteratedDeriv_eq]
  intro n
  have hn : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have horder : (n : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hn
  have hfder := (ofFunction_eq_iff_iteratedDeriv_eq m f₁ f₂ a a).mp hf n
  have hgder := (ofFunction_eq_iff_iteratedDeriv_eq m g₁ g₂ a a).mp hg n
  calc
    iteratedDeriv (n : ℕ) (fun x => f₁ x - g₁ x) a =
        iteratedDeriv (n : ℕ) f₁ a - iteratedDeriv (n : ℕ) g₁ a := by
      exact iteratedDeriv_sub (hf₁.of_le horder)
        (hg₁.of_le horder)
    _ = iteratedDeriv (n : ℕ) f₂ a - iteratedDeriv (n : ℕ) g₂ a := by
      rw [hfder, hgder]
    _ = iteratedDeriv (n : ℕ) (fun x => f₂ x - g₂ x) a := by
      exact (iteratedDeriv_sub (hf₂.of_le horder)
        (hg₂.of_le horder)).symm

end FiniteTaylorJet
