module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Defs

public section

namespace FiniteTaylorJet

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Helper for Infrastructure I.16a: coefficients of a finite jet built from a
smooth map vary continuously with the base point. -/
theorem continuous_ofFunction_coeff (m : ℕ) (f : E → F) (hf : ContDiff ℝ m f)
    (n : Fin (m + 1)) :
    Continuous (fun x : E ↦ (ofFunction ℝ m f x).coeff n) := by
  rw [show (fun x : E ↦ (ofFunction ℝ m f x).coeff n) =
      fun x ↦ ((n : ℕ).factorial : ℝ)⁻¹ • iteratedFDeriv ℝ (n : ℕ) f x by
    funext x
    exact coeff_ofFunction m f x n]
  have hscalar : Continuous (fun _ : E ↦ ((n : ℕ).factorial : ℝ)⁻¹) :=
    continuous_const
  have hn : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hnTop : ((n : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hn
  have hderiv : Continuous (fun x : E ↦ iteratedFDeriv ℝ (n : ℕ) f x) :=
    ContDiff.continuous_iteratedFDeriv hnTop hf
  exact hscalar.smul
    hderiv

/-- Helper for Infrastructure I.16a: continuity of degree-zero coefficient maps
implies continuity of the corresponding constant-coefficient family. -/
theorem continuous_constantCoeff_of_coeff_zero {α : Type u}
    [TopologicalSpace α] {m : ℕ} (P : α → FiniteTaylorJet ℝ ℝ F m)
    (hP : Continuous (fun a ↦ (P a).coeff (0 : Fin (m + 1)))) :
    Continuous (fun a ↦ (P a).constantCoeff) := by
  have hconstant_eq : (fun a ↦ (P a).constantCoeff) = fun a ↦
      (P a).coeff (0 : Fin (m + 1)) (fun _ ↦ 0) := by
    funext a
    exact constantCoeff_eq_coeff_zero (P a)
  rw [hconstant_eq]
  exact hP.eval continuous_const

/-- Helper for Infrastructure I.16a: coefficientwise continuous families of
finite jets remain coefficientwise continuous after pairing their values. -/
theorem continuous_prod_coeff {α : Type u} [TopologicalSpace α] {m : ℕ}
    (P : α → FiniteTaylorJet ℝ E F m) (Q : α → FiniteTaylorJet ℝ E G m)
    (hP : ∀ n : Fin (m + 1), Continuous (fun a ↦ (P a).coeff n))
    (hQ : ∀ n : Fin (m + 1), Continuous (fun a ↦ (Q a).coeff n))
    (n : Fin (m + 1)) :
    Continuous (fun a ↦ (prod (P a) (Q a)).coeff n) := by
  have hcoeff_eq : (fun a ↦ (prod (P a) (Q a)).coeff n) =
      fun a ↦ (P a).coeff n |>.prod ((Q a).coeff n) := by
    funext a
    exact coeff_prod (P a) (Q a) n
  rw [hcoeff_eq]
  exact (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin (n : ℕ) ↦ E) F G).continuous.comp
    ((hP n).prodMk (hQ n))

/-- Helper for Infrastructure I.16a: scalar evaluation of a continuous
one-variable coefficient family is continuous. -/
theorem continuous_scalarCoeff {α : Type u} [TopologicalSpace α]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    (P : α → FiniteTaylorJet ℝ ℝ F m)
    (hP : ∀ n : Fin (m + 1), Continuous (fun a ↦ (P a).coeff n))
    (n : Fin (m + 1)) :
    Continuous (fun a ↦ (P a).scalarCoeff n) := by
  have hcoeff := hP n
  have heq : (fun a ↦ (P a).scalarCoeff n) = fun a ↦
      (P a).coeff n (fun _ ↦ 1) := by
    funext a
    exact scalarCoeff_apply (P a) n
  rw [heq]
  exact hcoeff.eval continuous_const

/-- Helper for Infrastructure I.16a: a family of multilinear maps is continuous
when its evaluation on the all-ones vector is continuous. -/
theorem continuous_multilinearMap_of_apply_one {Y : Type v}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (f : ℝ → (ℝ [×n]→L[ℝ] Y))
    (hf : Continuous (fun u ↦ f u (fun _ ↦ 1))) : Continuous f := by
  have hfactor : f = fun u ↦
      ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) Y
        (f u (fun _ ↦ 1)) := by
    funext u
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) Y).apply_symm_apply
      (f u) |>.symm
  rw [hfactor]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) Y).continuous.comp hf

/-- Helper for Infrastructure I.16a: coefficientwise continuous scalar-source
jets remain coefficientwise continuous under finite Taylor composition. -/
theorem continuous_comp_coeff {F G : Type v}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : ℕ}
    (P : ℝ → FiniteTaylorJet ℝ ℝ F m)
    (Q : ℝ → FiniteTaylorJet ℝ F G m)
    (hP : ∀ n : Fin (m + 1), Continuous (fun u ↦ (P u).coeff n))
    (hQ : ∀ n : Fin (m + 1), Continuous (fun u ↦ (Q u).coeff n))
    (n : Fin (m + 1)) :
    Continuous (fun u ↦ (comp (Q u) (P u)).coeff n) := by
  apply continuous_multilinearMap_of_apply_one
  simp only [coeff_comp, FormalMultilinearSeries.comp,
    _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
  apply continuous_finsetSum
  intro c hc
  have hlengthOrder : c.length ≤ m :=
    c.length_le.trans (Nat.le_of_lt_succ n.isLt)
  have houter : Continuous (fun u ↦ (Q u).toFormalMultilinearSeries c.length) := by
    have houter_eq : (fun u ↦ (Q u).toFormalMultilinearSeries c.length) =
        fun u ↦ (Q u).coeff ⟨c.length, Nat.lt_succ_iff.mpr hlengthOrder⟩ := by
      funext u
      exact toFormalMultilinearSeries_coeff_of_le (Q u) hlengthOrder
    rw [houter_eq]
    exact hQ _
  have hinner (i : Fin c.length) :
      Continuous (fun u ↦ (P u).toFormalMultilinearSeries (c.blocksFun i)) := by
    have hblockOrder : c.blocksFun i ≤ m :=
      (c.blocksFun_le i).trans (Nat.le_of_lt_succ n.isLt)
    have hinner_eq :
        (fun u ↦ (P u).toFormalMultilinearSeries (c.blocksFun i)) =
          fun u ↦ (P u).coeff
            ⟨c.blocksFun i, Nat.lt_succ_iff.mpr hblockOrder⟩ := by
      funext u
      exact toFormalMultilinearSeries_coeff_of_le (P u) hblockOrder
    rw [hinner_eq]
    exact hP _
  have hinner_apply (i : Fin c.length) : Continuous (fun u ↦
      (P u).toFormalMultilinearSeries (c.blocksFun i) (fun _ ↦ (1 : ℝ))) :=
    (hinner i).eval continuous_const
  exact houter.eval (continuous_pi hinner_apply)

end FiniteTaylorJet
