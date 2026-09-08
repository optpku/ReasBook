module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Tactic.FunProp

public section

namespace FiniteTaylorJet

universe u

/-- A scalar-source multilinear-map family is `C¹` when its value on the
all-ones vector is `C¹`. -/
theorem contDiffOne_multilinearMap_of_apply_one
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (f : ℝ → (ℝ [×n]→L[ℝ] Y))
    (hf : ContDiff ℝ 1 (fun u ↦ f u (fun _ ↦ 1))) :
    ContDiff ℝ 1 f := by
  -- Scalar multilinear maps are continuously linearly equivalent to their
  -- value on the repeated-one vector, so transport the asserted regularity.
  have hfactor : f = fun u ↦
      ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) Y
        (f u (fun _ ↦ 1)) := by
    funext u
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) Y).apply_symm_apply
      (f u) |>.symm
  rw [hfactor]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) Y).contDiff.comp hf

/-- Coefficientwise `C¹` scalar-source finite jets remain coefficientwise
`C¹` after finite Taylor composition. -/
theorem contDiffOne_comp_coeff
    {F G : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : ℕ}
    (P : ℝ → FiniteTaylorJet ℝ ℝ F m)
    (Q : ℝ → FiniteTaylorJet ℝ F G m)
    (hP : ∀ n : Fin (m + 1), ContDiff ℝ 1 (fun u ↦ (P u).coeff n))
    (hQ : ∀ n : Fin (m + 1), ContDiff ℝ 1 (fun u ↦ (Q u).coeff n))
    (n : Fin (m + 1)) :
    ContDiff ℝ 1 (fun u ↦ (comp (Q u) (P u)).coeff n) := by
  -- Evaluate the scalar-source coefficient at repeated ones, where the
  -- composition formula is a finite sum of smooth multilinear evaluations.
  apply contDiffOne_multilinearMap_of_apply_one
  simp only [coeff_comp, FormalMultilinearSeries.comp,
    _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
  apply ContDiff.sum
  intro c hc
  have hlengthOrder : c.length ≤ m :=
    c.length_le.trans (Nat.le_of_lt_succ n.isLt)
  have houter : ContDiff ℝ 1
      (fun u ↦ (Q u).toFormalMultilinearSeries c.length) := by
    have houter_eq : (fun u ↦ (Q u).toFormalMultilinearSeries c.length) =
        fun u ↦ (Q u).coeff ⟨c.length, Nat.lt_succ_iff.mpr hlengthOrder⟩ := by
      funext u
      exact toFormalMultilinearSeries_coeff_of_le (Q u) hlengthOrder
    rw [houter_eq]
    exact hQ _
  have hinner (i : Fin c.length) : ContDiff ℝ 1
      (fun u ↦ (P u).toFormalMultilinearSeries (c.blocksFun i)) := by
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
  have hinner_apply (i : Fin c.length) : ContDiff ℝ 1 (fun u ↦
      (P u).toFormalMultilinearSeries (c.blocksFun i)
        (fun _ ↦ (1 : ℝ))) := by
    let evaluator :
        (ℝ [×c.blocksFun i]→L[ℝ] F) →L[ℝ] F :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin (c.blocksFun i) ↦ ℝ) F
        (fun _ ↦ (1 : ℝ))
    have heval := evaluator.contDiff.comp (hinner i)
    simpa only [Function.comp_def, evaluator,
      ContinuousMultilinearMap.apply_apply] using heval
  -- The multilinear evaluation operation is smooth in both the operator and
  -- its finite family of arguments.
  have heval : ContDiff ℝ 1 (fun p :
      (F [×c.length]→L[ℝ] G) × (Fin c.length → F) ↦ p.1 p.2) := by
    rw [← contDiffOn_univ]
    apply AnalyticOn.contDiffOn
      (ContinuousLinearMap.analyticOn_uncurry_of_multilinear
        (f := ContinuousLinearMap.id ℝ (F [×c.length]→L[ℝ] G)))
      uniqueDiffOn_univ
  have houter_pair : ContDiff ℝ 1 (fun u ↦
      ((Q u).toFormalMultilinearSeries c.length,
        fun i ↦ (P u).toFormalMultilinearSeries (c.blocksFun i)
          (fun _ ↦ (1 : ℝ)))) := by
    apply ContDiff.prodMk
    · exact houter
    · apply contDiff_pi.2
      intro i
      exact hinner_apply i
  exact heval.comp houter_pair

end FiniteTaylorJet
