module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder
public import Mathlib.Analysis.Calculus.ContDiff.Operations

public section

universe u v w

namespace FiniteTaylorJet

variable {Θ : Type u} {E : Type v} {F : Type w}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a fixed-parameter slice is the joint derivative restricted
to the canonical right inclusion, assuming only pointwise finite smoothness. -/
lemma iteratedFDeriv_slice_eq_comp_inr_at {m n : ℕ} {f : Θ → E → F}
    {θ : Θ} {a : E} (hf : ContDiffAt ℝ m (Function.uncurry f) (θ, a))
    (hn : n ≤ m) :
    iteratedFDeriv ℝ n (f θ) a =
      (iteratedFDeriv ℝ n (Function.uncurry f) (θ, a)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ Θ E) := by
  let shifted : Θ × E → F := fun z ↦ Function.uncurry f ((θ, 0) + z)
  have htranslation :
      ContDiffAt ℝ m (fun z : Θ × E ↦ (θ, 0) + z) (0, a) :=
    contDiffAt_const.add contDiffAt_id
  have hshifted : ContDiffAt ℝ m shifted (0, a) := by
    apply ContDiffAt.comp (f := fun z : Θ × E ↦ (θ, 0) + z)
      (g := Function.uncurry f) (0, a)
    · have hpoint : (θ, 0) + (0, a) = (θ, a) := by
        simp only [Prod.mk_add_mk, zero_add, add_zero]
      rw [hpoint]
      exact hf
    · simpa only [Function.comp_def, shifted] using htranslation
  have hwithinAt : ContDiffWithinAt ℝ m shifted Set.univ (0, a) :=
    hshifted.contDiffWithinAt
  have hfinite :
      (m : WithTop (WithTop ℕ)) =
          (↑(⊤ : WithTop ℕ) : WithTop (WithTop ℕ)) →
        (m : WithTop (WithTop ℕ)) = (⊤ : WithTop (WithTop ℕ)) := by
    intro hm
    have hm' : (m : WithTop ℕ) = (⊤ : WithTop ℕ) :=
      WithTop.coe_injective hm
    exact (WithTop.coe_ne_top (a := m) hm').elim
  obtain ⟨u, hu, hxu, hU⟩ :=
    hwithinAt.contDiffOn' le_rfl hfinite
  have hu' : ContDiffOn ℝ m shifted u := by
    have hset : insert (0, a) Set.univ ∩ u = u := by
      ext z
      simp
    rw [hset] at hU
    exact hU
  have hpre : IsOpen (ContinuousLinearMap.inr ℝ Θ E ⁻¹' u) :=
    hu.preimage (ContinuousLinearMap.continuous _)
  have hprex : a ∈ ContinuousLinearMap.inr ℝ Θ E ⁻¹' u := by
    change (0, a) ∈ u
    exact hxu
  have hdegree : (n : WithTop (WithTop ℕ)) ≤
      (m : WithTop (WithTop ℕ)) := by
    have hdegreeInner : (n : WithTop ℕ) ≤ (m : WithTop ℕ) :=
      WithTop.coe_le_coe.mpr hn
    exact WithTop.coe_le_coe.mpr hdegreeInner
  have hwithin := (ContinuousLinearMap.inr ℝ Θ E).iteratedFDerivWithin_comp_right
    hu' hu.uniqueDiffOn hpre.uniqueDiffOn hxu hdegree
  have hshiftWithin :
      iteratedFDeriv ℝ n shifted (0, a) =
        iteratedFDerivWithin ℝ n shifted u (0, a) := by
    symm
    simpa only [Set.univ_inter, iteratedFDerivWithin_univ] using
      (iteratedFDerivWithin_inter_open (f := shifted) (s := Set.univ)
        (u := u) hu hxu (𝕜 := ℝ) (n := n))
  have hpreEq := iteratedFDerivWithin_inter_open
    (f := shifted ∘ ContinuousLinearMap.inr ℝ Θ E)
    (s := Set.univ) (u := ContinuousLinearMap.inr ℝ Θ E ⁻¹' u)
    hpre hprex (𝕜 := ℝ) (n := n)
  have hpreEq' :
      iteratedFDerivWithin ℝ n (shifted ∘ ContinuousLinearMap.inr ℝ Θ E)
          (ContinuousLinearMap.inr ℝ Θ E ⁻¹' u) a =
        iteratedFDerivWithin ℝ n (shifted ∘ ContinuousLinearMap.inr ℝ Θ E)
          Set.univ a := by
    simpa only [Set.univ_inter] using hpreEq
  have hcompWithin :
      iteratedFDeriv ℝ n (shifted ∘ ContinuousLinearMap.inr ℝ Θ E) a =
        (iteratedFDerivWithin ℝ n shifted u (0, a)).compContinuousLinearMap
          (fun _ ↦ ContinuousLinearMap.inr ℝ Θ E) := by
    rw [← iteratedFDerivWithin_univ, ← hpreEq']
    simpa only [Set.univ_inter, ContinuousLinearMap.inr_apply] using hwithin
  have hslice :
      iteratedFDeriv ℝ n (f θ) a =
        iteratedFDeriv ℝ n (shifted ∘ ContinuousLinearMap.inr ℝ Θ E) a := by
    simp only [shifted, Function.comp_def, Function.uncurry_apply_pair,
      ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  rw [hslice, hcompWithin, ← hshiftWithin]
  simp only [shifted, Prod.mk_add_mk, add_zero, zero_add,
    iteratedFDeriv_comp_add_left]

/-- Pointwise joint `C^m` regularity on a compact parameter set gives one
uniform norm bound for every factorial-normalized Taylor coefficient. -/
theorem uniformCoeffBounds_of_contDiffAt (m : ℕ) (f : Θ → E → F) (a : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : ∀ θ ∈ K, ContDiffAt ℝ m (Function.uncurry f) (θ, a)) :
    ∀ n : Fin (m + 1), ∃ B ≥ 0, ∀ θ ∈ K,
      ‖(ofFunction ℝ m (f θ) a).coeff n‖ ≤ B := by
  intro n
  have hdegree : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hderivContinuous :
      ContinuousOn
        (fun θ : Θ ↦ iteratedFDeriv ℝ (n : ℕ)
          (Function.uncurry f) (θ, a)) K := by
    intro θ hθ
    have hdegree' : (n : WithTop (WithTop ℕ)) ≤
        (m : WithTop (WithTop ℕ)) := by
      have hdegreeInner : (n : WithTop ℕ) ≤ (m : WithTop ℕ) := by
        exact WithTop.coe_le_coe.mpr hdegree
      exact WithTop.coe_le_coe.mpr hdegreeInner
    have hjoint :
        ContinuousAt
          (iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f)) (θ, a) :=
      (hf θ hθ).continuousAt_iteratedFDeriv hdegree'
    have hfiber : ContinuousAt (fun θ' : Θ ↦ (θ', a)) θ :=
      continuousAt_id.prodMk continuousAt_const
    have hcompose := ContinuousAt.comp'
      (f := fun θ' : Θ ↦ (θ', a))
      (g := iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f))
      (x := θ) hjoint hfiber
    simpa only [Function.comp_def] using hcompose.continuousWithinAt
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hderivContinuous
  refine ⟨‖(((n : ℕ).factorial : ℝ)⁻¹)‖ * max R 0,
    mul_nonneg (norm_nonneg _) (le_max_right _ _), ?_⟩
  intro θ hθ
  rw [coeff_ofFunction, iteratedFDeriv_slice_eq_comp_inr_at
    (hf θ hθ) hdegree, norm_smul]
  have hrestriction :
      ‖(iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)).compContinuousLinearMap
          (fun _ ↦ ContinuousLinearMap.inr ℝ Θ E)‖ ≤
        ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ := by
    calc
      ‖(iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)).compContinuousLinearMap
          (fun _ ↦ ContinuousLinearMap.inr ℝ Θ E)‖
          ≤ ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ *
              ∏ _i : Fin (n : ℕ), ‖ContinuousLinearMap.inr ℝ Θ E‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ *
            ∏ _i : Fin (n : ℕ), 1 := by
        gcongr
        exact ContinuousLinearMap.norm_inr_le_one ℝ Θ E
      _ = ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ := by
        simp only [Finset.prod_const_one, mul_one]
  exact mul_le_mul_of_nonneg_left
    (hrestriction.trans ((hR θ hθ).trans (le_max_left R 0))) (norm_nonneg _)

/-- The compact-fiber coefficient bounds and the standard uniform remainder
estimate can be consumed together as the two clauses of a uniform jet proof. -/
theorem uniformJetData_of_contDiffAt (m : ℕ) (f : Θ → E → F) (a : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : ∀ θ ∈ K, ContDiffAt ℝ m (Function.uncurry f) (θ, a)) :
    (∀ n : Fin (m + 1), ∃ B ≥ 0, ∀ θ ∈ K,
      ‖(ofFunction ℝ m (f θ) a).coeff n‖ ≤ B) ∧
      ∀ C > 0, IsUniformRemainderOn f
        (fun θ ↦ ofFunction ℝ m (f θ) a) a K C (m : ℝ) := by
  constructor
  · exact uniformCoeffBounds_of_contDiffAt m f a K hK hf
  · intro C hC
    exact uniformRemainderOn_of_contDiffAt m f a K hK hf C hC

end FiniteTaylorJet
