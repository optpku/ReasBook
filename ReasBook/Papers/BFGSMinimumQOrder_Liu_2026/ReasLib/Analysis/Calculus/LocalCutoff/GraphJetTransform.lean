module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphTransform
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.OfFunctionOperations
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Continuity
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.ScalarComposition
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.TopCoefficientProjection
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.SectionContraction
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.UniformLimit
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FixedSectionDerivativeBridge
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.PredecessorSecantLowOrder
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ProofSupport.AffineCocycle
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ProofSupport.AffineFiniteJet
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Normed.Group.Bounded

public section

open scoped NNReal
open scoped Topology
open scoped Pointwise
open Filter
open Asymptotics

universe u v w

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {radius slope : ℝ≥0}

/-- A bounded order-`r` jet section over a small Lipschitz graph.  The zeroth
coefficient is required to recover the graph, while the higher coefficients
are independent bounded data used in the finite-smooth induction. -/
structure BoundedGraphJet (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (radius slope : ℝ≥0) (r : ℕ) where
  graph : SmallLipschitzGraph X radius slope
  jet : ℝ → FiniteTaylorJet ℝ ℝ X r
  coeffBound : Fin (r + 1) → ℝ≥0
  constantCoeff_eq : ∀ u, (jet u).constantCoeff = graph u
  coeff_le : ∀ u n, ‖(jet u).coeff n‖ ≤ (coeffBound n : ℝ)

namespace BoundedGraphJet

/-- Bundle an explicitly bounded jet family over a small graph. -/
def ofJets (graph : SmallLipschitzGraph X radius slope)
    (jet : ℝ → FiniteTaylorJet ℝ ℝ X r) (coeffBound : Fin (r + 1) → ℝ≥0)
    (constantCoeff_eq : ∀ u, (jet u).constantCoeff = graph u)
    (coeff_le : ∀ u n, ‖(jet u).coeff n‖ ≤ (coeffBound n : ℝ)) :
    BoundedGraphJet X radius slope r where
  graph := graph
  jet := jet
  coeffBound := coeffBound
  constantCoeff_eq := constantCoeff_eq
  coeff_le := coeff_le

end BoundedGraphJet

namespace JetTransform

/-- The constant coefficient of a finite-jet composition is the constant
coefficient of its outer jet. -/
private theorem finiteTaylorJet_constantCoeff_comp
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q : FiniteTaylorJet ℝ F G m) (P : FiniteTaylorJet ℝ E F m) :
    (FiniteTaylorJet.comp Q P).constantCoeff = Q.constantCoeff := by
  rw [FiniteTaylorJet.constantCoeff_eq_coeff_zero,
    FiniteTaylorJet.constantCoeff_eq_coeff_zero, FiniteTaylorJet.coeff_comp]
  have hzero := FormalMultilinearSeries.comp_coeff_zero Q.toFormalMultilinearSeries
    P.toFormalMultilinearSeries (fun _ : Fin 0 ↦ (0 : E)) (fun _ : Fin 0 ↦ (0 : F))
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q (Nat.zero_le m)] at hzero
  convert hzero using 1 <;> rfl

/-- Pairing two finite jets pairs their constant coefficients. -/
private theorem finiteTaylorJet_constantCoeff_prod
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (P : FiniteTaylorJet ℝ E F m) (Q : FiniteTaylorJet ℝ E G m) :
    (FiniteTaylorJet.prod P Q).constantCoeff = (P.constantCoeff, Q.constantCoeff) := by
  rw [FiniteTaylorJet.constantCoeff_eq_coeff_zero,
    FiniteTaylorJet.constantCoeff_eq_coeff_zero,
    FiniteTaylorJet.constantCoeff_eq_coeff_zero, FiniteTaylorJet.coeff_prod]
  rfl

/-- Positive-degree coefficients of a finite-jet composition are bounded by
uniform bounds for the outer coefficients and the positive inner coefficients. -/
private theorem finiteTaylorJet_norm_coeff_comp_le_of_pos
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q : FiniteTaylorJet ℝ F G m) (P : FiniteTaylorJet ℝ E F m)
    (BP BQ : ℝ) (hBQ : 0 ≤ BQ)
    (hP : ∀ k : Fin (m + 1), 0 < (k : ℕ) → ‖P.coeff k‖ ≤ BP)
    (hQ : ∀ k : Fin (m + 1), 0 < (k : ℕ) → ‖Q.coeff k‖ ≤ BQ)
    (n : Fin (m + 1)) (hn : 0 < (n : ℕ)) :
    ‖(FiniteTaylorJet.comp Q P).coeff n‖ ≤
      ∑ c : Composition (n : ℕ), BQ * BP ^ c.length := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]
  calc
    ‖∑ c : Composition (n : ℕ),
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c‖ ≤
        ∑ c : Composition (n : ℕ),
          ‖Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : Composition (n : ℕ), BQ * BP ^ c.length := by
      apply Finset.sum_le_sum
      intro c _
      calc
        ‖Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c‖ ≤
            ‖Q.toFormalMultilinearSeries c.length‖ *
              ∏ i, ‖P.toFormalMultilinearSeries (c.blocksFun i)‖ :=
          FormalMultilinearSeries.compAlongComposition_norm _ _ _
        _ ≤ BQ * ∏ _i : Fin c.length, BP := by
          apply mul_le_mul
          · rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q
              (c.length_le.trans (Nat.le_of_lt_succ n.isLt))]
            exact hQ ⟨c.length, (c.length_le.trans_lt n.isLt)⟩
              (c.length_pos_of_pos hn)
          · apply Finset.prod_le_prod
            · intro i _
              exact norm_nonneg _
            · intro i _
              rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P
                ((c.blocksFun_le i).trans (Nat.le_of_lt_succ n.isLt))]
              exact hP ⟨c.blocksFun i, (c.blocksFun_le i).trans_lt n.isLt⟩
                (c.one_le_blocksFun i)
          · exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
          · exact hBQ
        _ = BQ * BP ^ c.length := by
          simp only [Finset.prod_const, Finset.card_fin]

/-- Every positive iterated Fréchet derivative of a continuous linear map has
operator norm at most the norm of the map. -/
private theorem norm_iteratedFDeriv_continuousLinearMap_le
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (n : ℕ) (hn : 0 < n) (x : E) :
    ‖iteratedFDeriv ℝ n A x‖ ≤ ‖A‖ := by
  obtain _ | _ | n := n
  · omega
  · rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
  · rw [← norm_iteratedFDeriv_fderiv]
    rw [show fderiv ℝ A = fun _ ↦ A by
      funext y
      exact ContinuousLinearMap.fderiv A]
    rw [iteratedFDeriv_const_of_ne (by omega)]
    simp

/-- The order-`r` jet of the parametrized graph `u ↦ (u, ζ u)`, formed from
the identity jet and the stored graph jet. -/
noncomputable def graphParametrizationJet (r : ℕ) (J : BoundedGraphJet X radius slope r)
    (u : ℝ) : FiniteTaylorJet ℝ ℝ (ℝ × X) r :=
  FiniteTaylorJet.prod (FiniteTaylorJet.ofFunction ℝ r id u) (J.jet u)

/-- The order-`r` jet of the center-stable cutoff map along a bounded graph jet. -/
noncomputable def imageJet (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J : BoundedGraphJet X radius slope r) (u : ℝ) :
    FiniteTaylorJet ℝ ℝ (ℝ × X) r :=
  FiniteTaylorJet.postcomp (LocalCutoff.centerStableLinearize χ ρ L N)
    (graphParametrizationJet r J u)

/-- The center component of the differentiated cutoff map along a graph jet. -/
noncomputable def centerJet (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J : BoundedGraphJet X radius slope r) (u : ℝ) :
    FiniteTaylorJet ℝ ℝ ℝ r :=
  FiniteTaylorJet.postcomp Prod.fst (imageJet r χ ρ L N J u)

/-- The stable component of the differentiated cutoff map along a graph jet. -/
noncomputable def stableJet (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J : BoundedGraphJet X radius slope r) (u : ℝ) :
    FiniteTaylorJet ℝ ℝ X r :=
  FiniteTaylorJet.postcomp Prod.snd (imageJet r χ ρ L N J u)

/-- The differentiated order-`r` graph transform: compose the stable image jet
with the concrete finite jet of the inverse center projection. -/
noncomputable def differentiatedJet (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J : BoundedGraphJet X radius slope r) (ū : ℝ) :
    FiniteTaylorJet ℝ ℝ X r :=
  let u := LocalCutoff.CenterProjection.inverse χ ρ L N J.graph ū
  FiniteTaylorJet.comp (stableJet r χ ρ L N J u)
    (FiniteTaylorJet.ofFunction ℝ r
      (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) ū)

/-- The concrete coefficient bound of a transformed jet is the supremum of
the corresponding coefficient norm over the center parameter. -/
noncomputable def transformedCoeffBound (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (J : BoundedGraphJet X radius slope r) (n : Fin (r + 1)) : ℝ≥0 :=
  Real.toNNReal (sSup (Set.range fun ū ↦ ‖(differentiatedJet r χ ρ L N J ū).coeff n‖))

/-- Replace the top coefficient of a finite graph jet by a prescribed section. -/
noncomputable def topUpdatedFiniteJet (r : ℕ) (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (u : ℝ) : FiniteTaylorJet ℝ ℝ X r :=
  { coeff := Function.update (J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ (a u) }

/-- Replacing a positive-order top coefficient preserves the constant coefficient. -/
theorem topUpdatedFiniteJet_constantCoeff (r : ℕ) (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (u : ℝ) :
    (topUpdatedFiniteJet r J a u).constantCoeff = J.graph u := by
  -- Degree zero lies strictly below the updated positive top degree.
  rw [FiniteTaylorJet.constantCoeff_eq_coeff_zero]
  simp only [topUpdatedFiniteJet]
  rw [Function.update_of_ne]
  · simpa only [FiniteTaylorJet.constantCoeff_eq_coeff_zero] using J.constantCoeff_eq u
  · intro hzero
    have : (0 : ℕ) = r := congrArg Fin.val hzero
    omega

/-- Every coefficient below the top degree is unchanged by a top update. -/
theorem topUpdatedFiniteJet_coeff_of_lt (r : ℕ) (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
    (topUpdatedFiniteJet r J a u).coeff n = (J.jet u).coeff n := by
  -- The directed update rewrite avoids unfolding any other jet component.
  simp only [topUpdatedFiniteJet]
  rw [Function.update_of_ne]
  intro htop
  have : (n : ℕ) = r := congrArg Fin.val htop
  omega

/-- The top coefficient of a top-updated finite jet is the prescribed value. -/
theorem topUpdatedFiniteJet_topCoeff (r : ℕ) (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (u : ℝ) :
    (topUpdatedFiniteJet r J a u).coeff ⟨r, Nat.lt_succ_self r⟩ = a u := by
  -- At the updated index, `Function.update` computes directly.
  simp only [topUpdatedFiniteJet]
  rw [Function.update_self]

/-- The updated coefficient family is bounded by the old bounds below the top
degree and by the sup norm of the new top section at the top degree. -/
theorem topUpdatedFiniteJet_coeff_le (r : ℕ) (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (u : ℝ) (n : Fin (r + 1)) :
    ‖(topUpdatedFiniteJet r J a u).coeff n‖ ≤
      ((Function.update J.coeffBound ⟨r, Nat.lt_succ_self r⟩ ‖a‖₊) n : ℝ) := by
  -- Split only on the updated index, using the BCF sup bound in the top case.
  simp only [topUpdatedFiniteJet]
  by_cases htop : n = ⟨r, Nat.lt_succ_self r⟩
  · subst n
    rw [Function.update_self, Function.update_self]
    exact a.norm_coe_le_norm u
  · rw [Function.update_of_ne htop, Function.update_of_ne htop]
    exact J.coeff_le u n

/-- A bounded graph jet with only its top coefficient replaced by a bounded
continuous section. -/
noncomputable def topUpdatedGraphJet (r : ℕ) (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) :
    BoundedGraphJet X radius slope r :=
  BoundedGraphJet.ofJets J.graph (topUpdatedFiniteJet r J a)
    (Function.update J.coeffBound ⟨r, Nat.lt_succ_self r⟩ ‖a‖₊)
    (topUpdatedFiniteJet_constantCoeff r hr J a)
    (topUpdatedFiniteJet_coeff_le r J a)

/-- A top update preserves the underlying graph. -/
theorem topUpdatedGraphJet_graph (r : ℕ) (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) :
    (topUpdatedGraphJet r hr J a).graph = J.graph := by
  -- The graph field is inherited verbatim from the original bounded jet.
  rfl

/-- A top-updated bounded graph jet agrees with the original jet below the top degree. -/
theorem topUpdatedGraphJet_coeff_of_lt (r : ℕ) (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
    ((topUpdatedGraphJet r hr J a).jet u).coeff n = (J.jet u).coeff n := by
  -- Reduce the bundled projection to the finite-jet coefficient specification.
  exact topUpdatedFiniteJet_coeff_of_lt r J a u n hn

/-- The top coefficient of a top-updated bounded graph jet is the prescribed section. -/
theorem topUpdatedGraphJet_topCoeff (r : ℕ) (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (u : ℝ) :
    ((topUpdatedGraphJet r hr J a).jet u).coeff ⟨r, Nat.lt_succ_self r⟩ = a u := by
  -- Reduce the bundled projection to the finite-jet top update.
  exact topUpdatedFiniteJet_topCoeff r J a u

/-- Replacing the top coefficient by a bounded continuous section preserves
coefficientwise continuity of a bounded graph jet. -/
theorem continuous_topUpdatedGraphJet_coeff (r : ℕ) (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (hJ : ∀ n : Fin (r + 1), Continuous (fun u ↦ (J.jet u).coeff n))
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (n : Fin (r + 1)) :
    Continuous (fun u ↦ ((topUpdatedGraphJet r hr J a).jet u).coeff n) := by
  -- Separate the prescribed top section from the unchanged lower coefficients.
  by_cases htop : n = ⟨r, Nat.lt_succ_self r⟩
  · subst n
    simpa only [topUpdatedGraphJet_topCoeff] using a.continuous
  · have hn : (n : ℕ) < r := by
      have hn_le : (n : ℕ) ≤ r := Nat.le_of_lt_succ n.isLt
      have hn_ne : (n : ℕ) ≠ r := by
        intro hn_eq
        apply htop
        exact Fin.ext hn_eq
      omega
    have hcoeff : (fun u ↦ ((topUpdatedGraphJet r hr J a).jet u).coeff n) =
        fun u ↦ (J.jet u).coeff n := by
      funext u
      exact topUpdatedGraphJet_coeff_of_lt r hr J a u n hn
    rw [hcoeff]
    exact hJ n

/-- Under the finite-order smoothness and inverse-center hypotheses, every
coefficient family of the differentiated jet is bounded. -/
theorem differentiatedJet_bddAbove (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X) (lower : ℝ≥0)
    (J : BoundedGraphJet X radius slope r)
    (hrν : r ≤ ν) (hχ_smooth : ContDiff ℝ ν χ) (hχ_support : HasCompactSupport χ)
    (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ContDiff ℝ ν
      (LocalCutoff.CenterProjection.map χ ρ L N J.graph))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ u, (lower : ℝ) ≤
      deriv (LocalCutoff.CenterProjection.map χ ρ L N J.graph) u)
    (n : Fin (r + 1)) :
    BddAbove (Set.range fun ū ↦ ‖(differentiatedJet r χ ρ L N J ū).coeff n‖) := by
  classical
  have hcutoff_smooth : ContDiff ℝ ν (fun p : ℝ × X ↦ χ (ρ⁻¹ • p)) :=
    hχ_smooth.comp (contDiff_const_smul ρ⁻¹)
  have hremainder_eq : LocalCutoff.remainder χ ρ N =
      (fun p : ℝ × X ↦ χ (ρ⁻¹ • p)) • N := by
    funext p
    exact LocalCutoff.remainder_apply χ ρ N p
  have hremainder_smooth : ContDiff ℝ ν (LocalCutoff.remainder χ ρ N) := by
    rw [hremainder_eq]
    exact hcutoff_smooth.smul hN_smooth
  have hcutoff_support : HasCompactSupport (fun p : ℝ × X ↦ χ (ρ⁻¹ • p)) :=
    hχ_support.comp_smul (inv_ne_zero hρ)
  have hremainder_support : HasCompactSupport (LocalCutoff.remainder χ ρ N) := by
    rw [hremainder_eq]
    exact hcutoff_support.smul_right
  have exists_remainderDerivBound (k : ℕ) (hk : k ≤ ν) :
      ∃ C : ℝ≥0, ∀ p, ‖iteratedFDeriv ℝ k (LocalCutoff.remainder χ ρ N) p‖ ≤ (C : ℝ) := by
    have hcontinuous := hremainder_smooth.continuous_iteratedFDeriv (by exact_mod_cast hk)
    obtain ⟨C, hC⟩ := hcontinuous.bounded_above_of_compact_support
      (hremainder_support.iteratedFDeriv k)
    have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    refine ⟨Real.toNNReal C, ?_⟩
    intro p
    rw [Real.coe_toNNReal C hC_nonneg]
    exact hC p
  let remainderDerivBound : ℕ → ℝ≥0 := fun k ↦
    if hk : k ≤ ν then Classical.choose (exists_remainderDerivBound k hk) else 0
  have hremainderDerivBound (k : ℕ) (hk : k ≤ ν) (p : ℝ × X) :
      ‖iteratedFDeriv ℝ k (LocalCutoff.remainder χ ρ N) p‖ ≤
        (remainderDerivBound k : ℝ) := by
    dsimp only [remainderDerivBound]
    rw [dif_pos hk]
    exact Classical.choose_spec (exists_remainderDerivBound k hk) p
  let centerMap := LocalCutoff.CenterProjection.map χ ρ L N J.graph
  let centerPerturbation : ℝ → ℝ := fun u ↦ centerMap u - u
  have hcenterPerturbation_smooth : ContDiff ℝ ν centerPerturbation := by
    simpa only [centerPerturbation, centerMap, id_eq] using h_center_smooth.sub contDiff_id
  obtain ⟨R, hR_nonneg, hcenterMap_eq⟩ :=
    LocalCutoff.CenterProjection.eq_id_of_abs_ge (radius := radius) (slope := slope)
      χ ρ L N hρ hχ_support
  have hcenterPerturbation_support : HasCompactSupport centerPerturbation := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
    intro u hu
    have hR_le : R ≤ |u| := by
      have hR_lt : R < |u| := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] using hu
      exact hR_lt.le
    simp only [centerPerturbation, centerMap, hcenterMap_eq J.graph u hR_le, sub_self]
  have exists_centerPerturbationDerivBound (k : ℕ) (hk : k ≤ ν) :
      ∃ C : ℝ≥0, ∀ u, ‖iteratedDeriv k centerPerturbation u‖ ≤ (C : ℝ) := by
    have hcontinuous := hcenterPerturbation_smooth.continuous_iteratedFDeriv
      (by exact_mod_cast hk)
    obtain ⟨C, hC⟩ := hcontinuous.bounded_above_of_compact_support
      (hcenterPerturbation_support.iteratedFDeriv k)
    have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    refine ⟨Real.toNNReal C, ?_⟩
    intro u
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rw [Real.coe_toNNReal C hC_nonneg]
    exact hC u
  let forwardBound : ℕ → ℝ≥0 := fun k ↦
    if hk : k ≤ ν then
      Classical.choose (exists_centerPerturbationDerivBound k hk) + 1
    else 0
  have hforwardBound (k : ℕ) (hk_pos : 0 < k) (hk : k ≤ ν) (u : ℝ) :
      ‖iteratedDeriv k centerMap u‖ ≤ (forwardBound k : ℝ) := by
    have hcenterMap_eq_add : centerMap = centerPerturbation + id := by
      funext x
      simp only [centerPerturbation, Pi.add_apply, id_eq, sub_add_cancel]
    have hperturbation_k : ContDiff ℝ k centerPerturbation :=
      hcenterPerturbation_smooth.of_le (by exact_mod_cast hk)
    have hid_k : ContDiff ℝ k (id : ℝ → ℝ) := contDiff_id
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hcenterMap_eq_add,
      iteratedFDeriv_add hperturbation_k hid_k]
    calc
      ‖iteratedFDeriv ℝ k centerPerturbation u + iteratedFDeriv ℝ k id u‖ ≤
          ‖iteratedFDeriv ℝ k centerPerturbation u‖ +
            ‖iteratedFDeriv ℝ k id u‖ := norm_add_le _ _
      _ ≤ ((Classical.choose (exists_centerPerturbationDerivBound k hk) : ℝ≥0) : ℝ) + 1 := by
        apply add_le_add
        · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          exact Classical.choose_spec (exists_centerPerturbationDerivBound k hk) u
        · simpa using norm_iteratedFDeriv_continuousLinearMap_le
            (ContinuousLinearMap.id ℝ ℝ) k hk_pos u
      _ = (forwardBound k : ℝ) := by
        simp only [forwardBound, dif_pos hk, NNReal.coe_add, NNReal.coe_one]
  let graphParametrizationCoeffBound : ℝ :=
    Finset.univ.sum fun k : Fin (r + 1) ↦
      ‖((k : ℕ).factorial : ℝ)⁻¹‖ + (J.coeffBound k : ℝ)
  have hgraphParametrizationCoeffBound_nonneg : 0 ≤ graphParametrizationCoeffBound := by
    dsimp only [graphParametrizationCoeffBound]
    exact Finset.sum_nonneg fun k _ ↦ add_nonneg (norm_nonneg _)
      (J.coeffBound k).coe_nonneg
  have hgraphParametrizationCoeffBound (u : ℝ) (k : Fin (r + 1))
      (hk_pos : 0 < (k : ℕ)) :
      ‖(graphParametrizationJet r J u).coeff k‖ ≤ graphParametrizationCoeffBound := by
    have hidCoeff :
        ‖(FiniteTaylorJet.ofFunction ℝ r id u).coeff k‖ ≤
          ‖((k : ℕ).factorial : ℝ)⁻¹‖ := by
      rw [FiniteTaylorJet.coeff_ofFunction, norm_smul]
      calc
        ‖((k : ℕ).factorial : ℝ)⁻¹‖ * ‖iteratedFDeriv ℝ (k : ℕ) id u‖ ≤
            ‖((k : ℕ).factorial : ℝ)⁻¹‖ * ‖ContinuousLinearMap.id ℝ ℝ‖ :=
          mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_continuousLinearMap_le
              (ContinuousLinearMap.id ℝ ℝ) (k : ℕ) hk_pos u) (norm_nonneg _)
        _ = ‖((k : ℕ).factorial : ℝ)⁻¹‖ := by simp
    rw [graphParametrizationJet, FiniteTaylorJet.coeff_prod,
      ContinuousMultilinearMap.opNorm_prod]
    apply (max_le (hidCoeff.trans (le_add_of_nonneg_right (J.coeffBound k).coe_nonneg))
      ((J.coeff_le u k).trans (le_add_of_nonneg_left (norm_nonneg _)))).trans
    simpa only [graphParametrizationCoeffBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin (r + 1) ↦
          ‖((i : ℕ).factorial : ℝ)⁻¹‖ + (J.coeffBound i : ℝ))
        (fun i _ ↦ add_nonneg (norm_nonneg _) (J.coeffBound i).coe_nonneg)
        (Finset.mem_univ k))
  let imageOuterCoeffBound : ℝ :=
    Finset.univ.sum fun k : Fin (r + 1) ↦ ‖((k : ℕ).factorial : ℝ)⁻¹‖ *
      (‖LocalCutoff.centerStable L‖ + (remainderDerivBound k : ℝ))
  have himageOuterCoeffBound_nonneg : 0 ≤ imageOuterCoeffBound := by
    dsimp only [imageOuterCoeffBound]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (remainderDerivBound k).coe_nonneg)
  have hlinearize_eq : LocalCutoff.centerStableLinearize χ ρ L N =
      LocalCutoff.centerStable L + LocalCutoff.remainder χ ρ N := by
    funext p
    rw [Pi.add_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.remainder_apply]
  have himageOuterCoeffBound (p : ℝ × X) (k : Fin (r + 1))
      (hk_pos : 0 < (k : ℕ)) :
      ‖(FiniteTaylorJet.ofFunction ℝ r (LocalCutoff.centerStableLinearize χ ρ L N) p).coeff k‖ ≤
        imageOuterCoeffBound := by
    have hkν : (k : ℕ) ≤ ν :=
      (Nat.le_of_lt_succ k.isLt).trans hrν
    have hlinear_smooth : ContDiff ℝ (k : ℕ) (LocalCutoff.centerStable L) :=
      (LocalCutoff.centerStable L).contDiff
    have hremainder_k : ContDiff ℝ (k : ℕ) (LocalCutoff.remainder χ ρ N) :=
      hremainder_smooth.of_le (by exact_mod_cast hkν)
    rw [FiniteTaylorJet.coeff_ofFunction, norm_smul, hlinearize_eq,
      iteratedFDeriv_add hlinear_smooth hremainder_k]
    calc
      ‖((k : ℕ).factorial : ℝ)⁻¹‖ *
          ‖iteratedFDeriv ℝ (k : ℕ) (LocalCutoff.centerStable L) p +
            iteratedFDeriv ℝ (k : ℕ) (LocalCutoff.remainder χ ρ N) p‖ ≤
          ‖((k : ℕ).factorial : ℝ)⁻¹‖ *
            (‖LocalCutoff.centerStable L‖ + (remainderDerivBound k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_add_le _ _).trans (add_le_add
          (norm_iteratedFDeriv_continuousLinearMap_le
            (LocalCutoff.centerStable L) (k : ℕ) hk_pos p)
          (hremainderDerivBound k hkν p))
      _ ≤ imageOuterCoeffBound := by
        simpa only [imageOuterCoeffBound] using
          (Finset.single_le_sum (s := Finset.univ)
            (f := fun i : Fin (r + 1) ↦ ‖((i : ℕ).factorial : ℝ)⁻¹‖ *
              (‖LocalCutoff.centerStable L‖ + (remainderDerivBound i : ℝ)))
            (fun i _ ↦ mul_nonneg (norm_nonneg _)
              (add_nonneg (norm_nonneg _) (remainderDerivBound i).coe_nonneg))
            (Finset.mem_univ k))
  let imageCoeffBound : ℝ :=
    Finset.univ.sum fun k : Fin (r + 1) ↦
      Finset.univ.sum fun c : Composition (k : ℕ) ↦
        imageOuterCoeffBound * graphParametrizationCoeffBound ^ c.length
  have himageCoeffBound_nonneg : 0 ≤ imageCoeffBound := by
    dsimp only [imageCoeffBound]
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      mul_nonneg himageOuterCoeffBound_nonneg
        (pow_nonneg hgraphParametrizationCoeffBound_nonneg _)
  have himageCoeffBound (u : ℝ) (k : Fin (r + 1)) (hk_pos : 0 < (k : ℕ)) :
      ‖(imageJet r χ ρ L N J u).coeff k‖ ≤ imageCoeffBound := by
    have hcomposition := finiteTaylorJet_norm_coeff_comp_le_of_pos
      (FiniteTaylorJet.ofFunction ℝ r (LocalCutoff.centerStableLinearize χ ρ L N)
        (graphParametrizationJet r J u).constantCoeff)
      (graphParametrizationJet r J u) graphParametrizationCoeffBound imageOuterCoeffBound
      himageOuterCoeffBound_nonneg (hgraphParametrizationCoeffBound u)
      (himageOuterCoeffBound (graphParametrizationJet r J u).constantCoeff) k hk_pos
    rw [imageJet, FiniteTaylorJet.postcomp_def]
    exact hcomposition.trans (by
      simpa only [imageCoeffBound] using
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun i : Fin (r + 1) ↦
            ∑ c : Composition (i : ℕ),
              imageOuterCoeffBound * graphParametrizationCoeffBound ^ c.length)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
            mul_nonneg himageOuterCoeffBound_nonneg
              (pow_nonneg hgraphParametrizationCoeffBound_nonneg _))
          (Finset.mem_univ k)))
  let stableOuterCoeffBound : ℝ :=
    Finset.univ.sum fun k : Fin (r + 1) ↦ ‖((k : ℕ).factorial : ℝ)⁻¹‖ *
      ‖ContinuousLinearMap.snd ℝ ℝ X‖
  have hstableOuterCoeffBound_nonneg : 0 ≤ stableOuterCoeffBound := by
    dsimp only [stableOuterCoeffBound]
    exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hstableOuterCoeffBound (p : ℝ × X) (k : Fin (r + 1))
      (hk_pos : 0 < (k : ℕ)) :
      ‖(FiniteTaylorJet.ofFunction ℝ r Prod.snd p).coeff k‖ ≤ stableOuterCoeffBound := by
    rw [FiniteTaylorJet.coeff_ofFunction, norm_smul]
    apply (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_continuousLinearMap_le
        (ContinuousLinearMap.snd ℝ ℝ X) (k : ℕ) hk_pos p) (norm_nonneg _)).trans
    simpa only [stableOuterCoeffBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin (r + 1) ↦ ‖((i : ℕ).factorial : ℝ)⁻¹‖ *
          ‖ContinuousLinearMap.snd ℝ ℝ X‖)
        (fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ k))
  let stableCoeffBound : ℝ :=
    Finset.univ.sum fun k : Fin (r + 1) ↦
      Finset.univ.sum fun c : Composition (k : ℕ) ↦
        stableOuterCoeffBound * imageCoeffBound ^ c.length
  have hstableCoeffBound_nonneg : 0 ≤ stableCoeffBound := by
    dsimp only [stableCoeffBound]
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      mul_nonneg hstableOuterCoeffBound_nonneg (pow_nonneg himageCoeffBound_nonneg _)
  have hstableCoeffBound (u : ℝ) (k : Fin (r + 1)) (hk_pos : 0 < (k : ℕ)) :
      ‖(stableJet r χ ρ L N J u).coeff k‖ ≤ stableCoeffBound := by
    have hcomposition := finiteTaylorJet_norm_coeff_comp_le_of_pos
      (FiniteTaylorJet.ofFunction ℝ r Prod.snd (imageJet r χ ρ L N J u).constantCoeff)
      (imageJet r χ ρ L N J u) imageCoeffBound stableOuterCoeffBound
      hstableOuterCoeffBound_nonneg (himageCoeffBound u)
      (hstableOuterCoeffBound (imageJet r χ ρ L N J u).constantCoeff) k hk_pos
    rw [stableJet, FiniteTaylorJet.postcomp_def]
    exact hcomposition.trans (by
      simpa only [stableCoeffBound] using
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun i : Fin (r + 1) ↦
            ∑ c : Composition (i : ℕ), stableOuterCoeffBound * imageCoeffBound ^ c.length)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
            mul_nonneg hstableOuterCoeffBound_nonneg
              (pow_nonneg himageCoeffBound_nonneg _))
          (Finset.mem_univ k)))
  by_cases hn_zero : (n : ℕ) = 0
  · have hn_eq : n = 0 := Fin.ext hn_zero
    subst n
    refine ⟨‖L‖ * (radius : ℝ) + (remainderDerivBound 0 : ℝ), ?_⟩
    rintro _ ⟨ū, rfl⟩
    let u := LocalCutoff.CenterProjection.inverse χ ρ L N J.graph ū
    have hgraphParametrization :
        (graphParametrizationJet r J u).constantCoeff = (u, J.graph u) := by
      rw [graphParametrizationJet, finiteTaylorJet_constantCoeff_prod,
        FiniteTaylorJet.constantCoeff_ofFunction, J.constantCoeff_eq]
      rfl
    have himage :
        (imageJet r χ ρ L N J u).constantCoeff =
          LocalCutoff.centerStableLinearize χ ρ L N (u, J.graph u) := by
      rw [imageJet, FiniteTaylorJet.postcomp_def, finiteTaylorJet_constantCoeff_comp,
        FiniteTaylorJet.constantCoeff_ofFunction, hgraphParametrization]
    have hstable :
        (stableJet r χ ρ L N J u).constantCoeff =
          (LocalCutoff.centerStableLinearize χ ρ L N (u, J.graph u)).2 := by
      rw [stableJet, FiniteTaylorJet.postcomp_def, finiteTaylorJet_constantCoeff_comp,
        FiniteTaylorJet.constantCoeff_ofFunction, himage]
    have hdifferentiated :
        (differentiatedJet r χ ρ L N J ū).constantCoeff =
          L (J.graph u) + (LocalCutoff.remainder χ ρ N (u, J.graph u)).2 := by
      rw [differentiatedJet, finiteTaylorJet_constantCoeff_comp, hstable,
        hlinearize_eq, Pi.add_apply, LocalCutoff.centerStable_apply]
      rfl
    have hgraph_norm : ‖J.graph u‖ ≤ (radius : ℝ) :=
      (BoundedContinuousFunction.norm_coe_le_norm
        (J.graph : BoundedContinuousFunction ℝ X) u).trans
        (SmallLipschitzGraph.norm_le J.graph)
    have hlinear : ‖L (J.graph u)‖ ≤ ‖L‖ * (radius : ℝ) :=
      (L.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hgraph_norm (norm_nonneg L))
    have hremainder :
        ‖(LocalCutoff.remainder χ ρ N (u, J.graph u)).2‖ ≤
          (remainderDerivBound 0 : ℝ) := by
      apply (norm_snd_le _).trans
      simpa only [norm_iteratedFDeriv_zero] using
        (hremainderDerivBound 0 (Nat.zero_le ν) (u, J.graph u))
    have hcoeff_zero :
        ‖(differentiatedJet r χ ρ L N J ū).coeff (0 : Fin (r + 1))‖ =
          ‖(differentiatedJet r χ ρ L N J ū).constantCoeff‖ := by
      calc
        ‖(differentiatedJet r χ ρ L N J ū).coeff (0 : Fin (r + 1))‖ =
            ‖(differentiatedJet r χ ρ L N J ū).coeff (0 : Fin (r + 1))
              (fun _ : Fin 0 ↦ (0 : ℝ))‖ :=
          (ContinuousMultilinearMap.fin0_apply_norm
            ((differentiatedJet r χ ρ L N J ū).coeff (0 : Fin (r + 1)))
            (x := fun _ : Fin 0 ↦ (0 : ℝ))).symm
        _ = ‖(differentiatedJet r χ ρ L N J ū).constantCoeff‖ :=
          congrArg norm
            (FiniteTaylorJet.constantCoeff_eq_coeff_zero
              (differentiatedJet r χ ρ L N J ū)).symm
    have hbound :
        ‖(differentiatedJet r χ ρ L N J ū).coeff (0 : Fin (r + 1))‖ ≤
          ‖L‖ * (radius : ℝ) + (remainderDerivBound 0 : ℝ) := by
      rw [hcoeff_zero, hdifferentiated]
      exact (norm_add_le _ _).trans (add_le_add hlinear hremainder)
    exact hbound
  · have hn_pos : 0 < (n : ℕ) := Nat.pos_of_ne_zero hn_zero
    have hr_pos : 1 ≤ r := by omega
    have hν_pos : 1 ≤ ν := hr_pos.trans hrν
    obtain ⟨inverseBound, _hinverseBound_one, hinverseBound⟩ :=
      Real.exists_uniform_iteratedDeriv_invFun_bound
        (I := Unit) (f := fun _ ↦ centerMap) hν_pos
        (fun _ ↦ h_center_smooth) h_lower_pos (fun _ ↦ h_lower)
        (fun j hj_two hjν _ u ↦ hforwardBound j (by omega) hjν u)
    let inverseCoeffBound : ℝ :=
      Finset.univ.sum fun k : Fin (r + 1) ↦
        ‖((k : ℕ).factorial : ℝ)⁻¹‖ * (inverseBound k : ℝ)
    have hinverseCoeffBound_nonneg : 0 ≤ inverseCoeffBound := by
      dsimp only [inverseCoeffBound]
      exact Finset.sum_nonneg fun _ _ ↦
        mul_nonneg (norm_nonneg _) (inverseBound _).coe_nonneg
    have hinverseCoeffBound (ū : ℝ) (k : Fin (r + 1))
        (hk_pos : 0 < (k : ℕ)) :
        ‖(FiniteTaylorJet.ofFunction ℝ r
          (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) ū).coeff k‖ ≤
            inverseCoeffBound := by
      have hkν : (k : ℕ) ≤ ν :=
        (Nat.le_of_lt_succ k.isLt).trans hrν
      have hinverse :
          ‖iteratedFDeriv ℝ (k : ℕ)
            (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) ū‖ ≤
              (inverseBound k : ℝ) := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          LocalCutoff.CenterProjection.inverse_def]
        exact hinverseBound (k : ℕ) hk_pos hkν () ū
      rw [FiniteTaylorJet.coeff_ofFunction, norm_smul]
      apply (mul_le_mul_of_nonneg_left hinverse (norm_nonneg _)).trans
      simpa only [inverseCoeffBound] using
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun i : Fin (r + 1) ↦
            ‖((i : ℕ).factorial : ℝ)⁻¹‖ * (inverseBound i : ℝ))
          (fun i _ ↦ mul_nonneg (norm_nonneg _) (inverseBound i).coe_nonneg)
          (Finset.mem_univ k))
    refine ⟨∑ c : Composition (n : ℕ),
      stableCoeffBound * inverseCoeffBound ^ c.length, ?_⟩
    rintro _ ⟨ū, rfl⟩
    have hcomposition := finiteTaylorJet_norm_coeff_comp_le_of_pos
      (stableJet r χ ρ L N J
        (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph ū))
      (FiniteTaylorJet.ofFunction ℝ r
        (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) ū)
      inverseCoeffBound stableCoeffBound hstableCoeffBound_nonneg
      (hinverseCoeffBound ū)
      (hstableCoeffBound
        (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph ū)) n hn_pos
    simpa only [differentiatedJet] using hcomposition

/-- The supremum bound contains every coefficient of the differentiated jet. -/
theorem differentiatedJet_coeff_le (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (J : BoundedGraphJet X radius slope r)
    (h_bdd : ∀ n, BddAbove
      (Set.range fun ū ↦ ‖(differentiatedJet r χ ρ L N J ū).coeff n‖))
    (u : ℝ) (n : Fin (r + 1)) :
    ‖(differentiatedJet r χ ρ L N J u).coeff n‖ ≤
      (transformedCoeffBound r χ ρ L N J n : ℝ) := by
  have hsSup_nonneg : 0 ≤ sSup
      (Set.range fun ū ↦ ‖(differentiatedJet r χ ρ L N J ū).coeff n‖) :=
    (norm_nonneg _).trans (le_csSup (h_bdd n) ⟨u, rfl⟩)
  rw [transformedCoeffBound, Real.coe_toNNReal]
  · exact le_csSup (h_bdd n) ⟨u, rfl⟩
  · exact hsSup_nonneg

/-- The constant coefficient of the differentiated jet is the ordinary graph
transform evaluated at the same center parameter. -/
theorem differentiatedJet_constantCoeff (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (J : BoundedGraphJet X radius slope r) (u : ℝ) :
    (differentiatedJet r χ ρ L N J u).constantCoeff =
      map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
        h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
        h_stable_lipschitz h_radius h_slope J.graph u := by
  let u₀ := LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u
  have hgraphParametrization :
      (graphParametrizationJet r J u₀).constantCoeff = (u₀, J.graph u₀) := by
    rw [graphParametrizationJet, finiteTaylorJet_constantCoeff_prod,
      FiniteTaylorJet.constantCoeff_ofFunction, J.constantCoeff_eq]
    rfl
  have himage :
      (imageJet r χ ρ L N J u₀).constantCoeff =
        LocalCutoff.centerStableLinearize χ ρ L N (u₀, J.graph u₀) := by
    rw [imageJet, FiniteTaylorJet.postcomp_def, finiteTaylorJet_constantCoeff_comp,
      FiniteTaylorJet.constantCoeff_ofFunction, hgraphParametrization]
  have hstable :
      (stableJet r χ ρ L N J u₀).constantCoeff =
        (LocalCutoff.centerStableLinearize χ ρ L N (u₀, J.graph u₀)).2 := by
    rw [stableJet, FiniteTaylorJet.postcomp_def, finiteTaylorJet_constantCoeff_comp,
      FiniteTaylorJet.constantCoeff_ofFunction, himage]
  rw [differentiatedJet, finiteTaylorJet_constantCoeff_comp, hstable,
    GraphTransform.map_apply]

/-- The concrete differentiated graph transform on bounded order-`r` jets. -/
noncomputable def map (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hrν : r ≤ ν) (hχ_smooth : ContDiff ℝ ν χ)
    (hχ_support : HasCompactSupport χ) (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (J : BoundedGraphJet X radius slope r) : BoundedGraphJet X radius slope r :=
  BoundedGraphJet.ofJets
    (GraphTransform.map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz
      h_radius h_slope J.graph)
    (differentiatedJet r χ ρ L N J) (transformedCoeffBound r χ ρ L N J)
    (differentiatedJet_constantCoeff r ν χ ρ L N lower linearRate stableBound
      stableCenter stableFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL
      h_stable_bound h_stable_lipschitz h_radius h_slope J)
    (differentiatedJet_coeff_le r χ ρ L N J
      (differentiatedJet_bddAbove r ν χ ρ L N lower J hrν hχ_smooth hχ_support
        hρ hN_smooth (h_center_smooth J.graph) h_lower_pos (h_lower J.graph)))

/-- The bounded jet transform has the ordinary graph transform as its base graph
and the differentiated composition formula as its jet family. -/
theorem map_spec (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hrν : r ≤ ν) (hχ_smooth : ContDiff ℝ ν χ)
    (hχ_support : HasCompactSupport χ) (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (J : BoundedGraphJet X radius slope r) :
    (map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
      hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL
      h_stable_bound h_stable_lipschitz h_radius h_slope J).graph =
        GraphTransform.map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
          h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
          h_stable_lipschitz h_radius h_slope J.graph ∧
    ∀ u, (map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
      hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL
      h_stable_bound h_stable_lipschitz h_radius h_slope J).jet u =
        differentiatedJet r χ ρ L N J u := by
  constructor
  · rfl
  · intro u
    rfl

/-- The uniform distance between one coefficient of two bounded graph jets. -/
noncomputable def coeffDistance {r : ℕ} (n : Fin (r + 1))
    (J K : BoundedGraphJet X radius slope r) : ℝ :=
  sSup (Set.range fun u ↦ ‖(J.jet u).coeff n - (K.jet u).coeff n‖)

/-- Every pointwise coefficient distance is bounded by the corresponding
uniform distance between two bounded graph jets. -/
theorem norm_coeff_sub_le_coeffDistance {r : ℕ} (n : Fin (r + 1))
    (J K : BoundedGraphJet X radius slope r) (u : ℝ) :
    ‖(J.jet u).coeff n - (K.jet u).coeff n‖ ≤ coeffDistance n J K := by
  -- The stored coefficient bounds provide the upper bound required by `le_csSup`.
  have hbounded : BddAbove
      (Set.range fun v ↦ ‖(J.jet v).coeff n - (K.jet v).coeff n‖) := by
    refine ⟨(J.coeffBound n : ℝ) + (K.coeffBound n : ℝ), ?_⟩
    rintro _ ⟨v, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (J.coeff_le v n) (K.coeff_le v n))
  exact le_csSup hbounded ⟨u, rfl⟩

/-- A uniform top-coefficient contraction between top-updated graph jets gives
the corresponding pointwise contraction of their prescribed top sections. -/
theorem topUpdatedGraphJet_topCoeff_dist_le_of_coeffDistance
    {r : ℕ} (hr : 0 < r) (J : BoundedGraphJet X radius slope r)
    (a b : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (T : BoundedGraphJet X radius slope r → BoundedGraphJet X radius slope r)
    (q : ℝ≥0)
    (hcontract : coeffDistance ⟨r, Nat.lt_succ_self r⟩
      (T (topUpdatedGraphJet r hr J a)) (T (topUpdatedGraphJet r hr J b)) ≤
        (q : ℝ) * coeffDistance ⟨r, Nat.lt_succ_self r⟩
          (topUpdatedGraphJet r hr J a) (topUpdatedGraphJet r hr J b))
    (u : ℝ) :
    dist (((T (topUpdatedGraphJet r hr J a)).jet u).coeff
        ⟨r, Nat.lt_succ_self r⟩)
      (((T (topUpdatedGraphJet r hr J b)).jet u).coeff
        ⟨r, Nat.lt_succ_self r⟩) ≤ (q : ℝ) * dist a b := by
  -- First enter the uniform jet metric, then identify the updated input tops.
  calc
    dist (((T (topUpdatedGraphJet r hr J a)).jet u).coeff
          ⟨r, Nat.lt_succ_self r⟩)
        (((T (topUpdatedGraphJet r hr J b)).jet u).coeff
          ⟨r, Nat.lt_succ_self r⟩) =
        ‖((T (topUpdatedGraphJet r hr J a)).jet u).coeff
            ⟨r, Nat.lt_succ_self r⟩ -
          ((T (topUpdatedGraphJet r hr J b)).jet u).coeff
            ⟨r, Nat.lt_succ_self r⟩‖ := dist_eq_norm _ _
    _ ≤ coeffDistance ⟨r, Nat.lt_succ_self r⟩
          (T (topUpdatedGraphJet r hr J a))
          (T (topUpdatedGraphJet r hr J b)) :=
      norm_coeff_sub_le_coeffDistance _ _ _ u
    _ ≤ (q : ℝ) * coeffDistance ⟨r, Nat.lt_succ_self r⟩
          (topUpdatedGraphJet r hr J a) (topUpdatedGraphJet r hr J b) := hcontract
    _ ≤ (q : ℝ) * dist a b := by
      apply mul_le_mul_of_nonneg_left
      · rw [coeffDistance]
        apply csSup_le
        · exact Set.range_nonempty _
        · rintro _ ⟨v, rfl⟩
          simpa only [topUpdatedGraphJet_topCoeff, dist_eq_norm] using
            (BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := b) v)
      · exact q.coe_nonneg

/-- The top coefficient obtained by applying a bounded-jet operator to a jet
whose top coefficient is a prescribed bounded continuous section. -/
noncomputable def topSectionValue {r : ℕ} (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (T : BoundedGraphJet X radius slope r → BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (u : ℝ) :
    ℝ [×r]→L[ℝ] X :=
  ((T (topUpdatedGraphJet r hr J a)).jet u).coeff ⟨r, Nat.lt_succ_self r⟩

/-- The stored bound of the transformed jet uniformly bounds its top-section value. -/
theorem topSectionValue_norm_le {r : ℕ} (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (T : BoundedGraphJet X radius slope r → BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (u : ℝ) :
    ‖topSectionValue hr J T a u‖ ≤
      ((T (topUpdatedGraphJet r hr J a)).coeffBound
        ⟨r, Nat.lt_succ_self r⟩ : ℝ) := by
  -- This is exactly the coefficient bound stored in the transformed bounded jet.
  exact (T (topUpdatedGraphJet r hr J a)).coeff_le u ⟨r, Nat.lt_succ_self r⟩

/-- Bundle a continuous transformed top-coefficient family as an operator on
bounded continuous sections. -/
noncomputable def topSectionOperator {r : ℕ} (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (T : BoundedGraphJet X radius slope r → BoundedGraphJet X radius slope r)
    (hcontinuous : ∀ a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X),
      Continuous (topSectionValue hr J T a)) :
    BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X) →
      BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X) :=
  fun a ↦ BoundedContinuousFunction.ofNormedAddCommGroup
    (topSectionValue hr J T a) (hcontinuous a)
    ((T (topUpdatedGraphJet r hr J a)).coeffBound
      ⟨r, Nat.lt_succ_self r⟩ : ℝ)
    (topSectionValue_norm_le hr J T a)

/-- Evaluation of the bundled top-section operator is the transformed top coefficient. -/
theorem topSectionOperator_apply {r : ℕ} (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (T : BoundedGraphJet X radius slope r → BoundedGraphJet X radius slope r)
    (hcontinuous : ∀ a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X),
      Continuous (topSectionValue hr J T a))
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (u : ℝ) :
    topSectionOperator hr J T hcontinuous a u = topSectionValue hr J T a u := by
  -- The bounded-function constructor preserves the underlying function definitionally.
  rfl

/-- A contracted transformed-top operator has a unique bounded continuous fixed section. -/
theorem existsUnique_fixedPoint_topSectionOperator {r : ℕ} (hr : 0 < r)
    (J : BoundedGraphJet X radius slope r)
    (T : BoundedGraphJet X radius slope r → BoundedGraphJet X radius slope r)
    (q : ℝ≥0) (hq : q < 1)
    (hcontinuous : ∀ a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X),
      Continuous (topSectionValue hr J T a))
    (hcontract : ∀ a b : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X),
      coeffDistance ⟨r, Nat.lt_succ_self r⟩
        (T (topUpdatedGraphJet r hr J a)) (T (topUpdatedGraphJet r hr J b)) ≤
          (q : ℝ) * coeffDistance ⟨r, Nat.lt_succ_self r⟩
            (topUpdatedGraphJet r hr J a) (topUpdatedGraphJet r hr J b)) :
    ∃! a, topSectionOperator hr J T hcontinuous a = a := by
  -- The pointwise bridge supplies exactly the BCF contraction hypothesis.
  apply BoundedContinuousFunction.existsUnique_fixedPoint_of_dist_apply_le_mul hq
  intro a b u
  simpa only [topSectionOperator_apply, topSectionValue] using
    topUpdatedGraphJet_topCoeff_dist_le_of_coeffDistance hr J a b T q
      (hcontract a b) u

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): when
two inner jets agree below a positive top order, only the one-block term of
their composed top coefficients can differ. -/
private theorem finiteTaylorJet_comp_topCoeff_sub_eq_inner
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet ℝ F G m)
    (P R : FiniteTaylorJet ℝ E F m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = R.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (continuousMultilinearCurryFin1 ℝ F G
        (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
          (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩) := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (Composition.single m hm)]
  · ext z
    change
      Q.toFormalMultilinearSeries.compAlongComposition P.toFormalMultilinearSeries
          (Composition.single m hm) z -
        Q.toFormalMultilinearSeries.compAlongComposition R.toFormalMultilinearSeries
          (Composition.single m hm) z = _
    rw [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.applyComposition_single,
      FormalMultilinearSeries.applyComposition_single,
      Composition.single_length,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hm)),
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P le_rfl,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      continuousMultilinearCurryFin1_apply]
    have hPvector : (fun _ : Fin 1 ↦ P.coeff ⟨m, Nat.lt_succ_self m⟩ z) =
        Fin.snoc 0 (P.coeff ⟨m, Nat.lt_succ_self m⟩ z) := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    have hRvector : (fun _ : Fin 1 ↦ R.coeff ⟨m, Nat.lt_succ_self m⟩ z) =
        Fin.snoc 0 (R.coeff ⟨m, Nat.lt_succ_self m⟩ z) := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    rw [hPvector, hRvector, ← continuousMultilinearCurryFin1_apply,
      ← continuousMultilinearCurryFin1_apply, ← map_sub]
    rw [continuousMultilinearCurryFin1_apply]
    rfl
  · intro c _ hc
    rw [sub_eq_zero]
    ext z
    simp only [FormalMultilinearSeries.compAlongComposition_apply]
    congr 1
    funext i
    dsimp only [FormalMultilinearSeries.applyComposition]
    have hblock : c.blocksFun i < m := (Composition.ne_single_iff hm).mp hc i
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P
        ((c.blocksFun_le i).trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R
        ((c.blocksFun_le i).trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
      hPR ⟨c.blocksFun i, hblock.trans (Nat.lt_succ_self m)⟩ hblock]
  · intro hsingle
    exact (hsingle (Finset.mem_univ _)).elim

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): the
top coefficient variation through a fixed outer jet is controlled by its
linear coefficient. -/
private theorem finiteTaylorJet_norm_comp_topCoeff_sub_le_inner
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet ℝ F G m)
    (P R : FiniteTaylorJet ℝ E F m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = R.coeff k) :
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
        ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  rw [finiteTaylorJet_comp_topCoeff_sub_eq_inner hm Q P R hPR]
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans_eq
  rw [LinearIsometryEquiv.norm_map]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): when
two outer jets agree below a positive top order, only the all-one-block term
of their composed top coefficients can differ. -/
private theorem finiteTaylorJet_comp_topCoeff_sub_eq_outer
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q R : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < m → Q.coeff k = R.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m) := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (Composition.ones m)]
  · ext z
    rfl
  · intro c _ hc
    rw [sub_eq_zero]
    have hlength_ne : c.length ≠ m := by
      intro hlength
      exact hc (Composition.eq_ones_iff_length.mpr hlength)
    have hlength : c.length < m := lt_of_le_of_ne c.length_le hlength_ne
    have hcoeff : Q.toFormalMultilinearSeries c.length =
        R.toFormalMultilinearSeries c.length := by
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q
          (c.length_le.trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R
          (c.length_le.trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
        hQR ⟨c.length, hlength.trans (Nat.lt_succ_self m)⟩ hlength]
    rw [FormalMultilinearSeries.compAlongComposition]
    exact congrArg (fun q ↦ q.compAlongComposition P.toFormalMultilinearSeries c) hcoeff
  · intro hones
    exact (hones (Finset.mem_univ _)).elim

/-- The all-one outer composition branch vanishes when the outer top
coefficient difference vanishes. -/
private theorem finiteTaylorJet_comp_topCoeff_outer_ones_eq_zero_of_topCoeff_eq
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q R : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m)
    (hTop : Q.coeff ⟨m, Nat.lt_succ_self m⟩ = R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m) = 0 := by
  -- Normalize the dependent outer coefficient at the length of `ones m`.
  ext z
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  have hcoeff :
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
          (Composition.ones m).length = 0 := by
    rw [Composition.ones_length]
    change Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m = 0
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl, hTop,
      sub_self]
  simpa only [hcoeff, zero_apply]

/-- Replacing only the top outer coefficient isolates the all-one composition
branch from the remaining equal-top residual. -/
private theorem finiteTaylorJet_comp_topCoeff_sub_eq_outer_through_topProjection
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ}
    (Q R Q' : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m)
    (hQ'lower : ∀ k : Fin (m + 1), (k : ℕ) < m → Q'.coeff k = Q.coeff k)
    (hQ'top : Q'.coeff ⟨m, Nat.lt_succ_self m⟩ = R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  -- First isolate the all-one term for the change from `Q` to the projected jet.
  have houter :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ =
        (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) :=
    finiteTaylorJet_comp_topCoeff_sub_eq_outer Q Q' P
      (fun k hk ↦ (hQ'lower k hk).symm)
  -- The all-one summand depends only on the top coefficient, so the projected
  -- jet contributes no all-one residual after its top coordinate is replaced.
  have hbranch :
      (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) =
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) := by
    ext z
    rw [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.compAlongComposition_apply]
    have hcoeff :
        (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries)
            (Composition.ones m).length =
          (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
            (Composition.ones m).length := by
      rw [Composition.ones_length]
      change Q.toFormalMultilinearSeries m - Q'.toFormalMultilinearSeries m =
        Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q' le_rfl,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl,
        hQ'top]
    exact congrArg
      (fun A : F [×(Composition.ones m).length]→L[ℝ] G ↦
        A (P.toFormalMultilinearSeries.applyComposition (Composition.ones m) z)) hcoeff
  -- Insert the mixed composition and normalize the additive expression.
  calc
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      abel
    _ = (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      rw [houter, hbranch]

/- The two-variable secant of a finite composition can be split into an inner
   variation followed by an outer variation.  This is the algebraic normal
   form used before applying the two specialized top-coefficient estimates. -/
private theorem finiteTaylorJet_comp_topCoeff_sub_decompose
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q R : FiniteTaylorJet ℝ F G m)
    (P S : FiniteTaylorJet ℝ E F m) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  -- Insert the mixed composition as an intermediate point and normalize the
  -- resulting additive expression at the multilinear-map level.
  abel

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): inserting
    an inner jet with the lower coefficients of `P` and the top coefficient of
    `R` separates the one-block predecessor term from the remaining composition
    residual. -/
private theorem finiteTaylorJet_comp_topCoeff_sub_eq_inner_through_topProjection
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet ℝ F G m)
    (P R P' : FiniteTaylorJet ℝ E F m)
    (hP'lower : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = P'.coeff k)
    (hP'top : P'.coeff ⟨m, Nat.lt_succ_self m⟩ = R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (continuousMultilinearCurryFin1 ℝ F G
        (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
          (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q P').coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  -- Insert the projected inner jet and use the equal-lower-coefficient formula.
  calc
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q P').coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q P').coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      abel
    _ = (continuousMultilinearCurryFin1 ℝ F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              P'.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q P').coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      rw [finiteTaylorJet_comp_topCoeff_sub_eq_inner hm Q P P' hP'lower]
    _ = (continuousMultilinearCurryFin1 ℝ F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q P').coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      rw [hP'top]

/-- The top coefficient of a finite composition is the finite sum indexed by
    compositions of the target order. -/
private theorem finiteTaylorJet_comp_topCoeff_branch_sum
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ∑ c : Composition m,
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c := by
  -- Unfold only the coefficient-level composition formula.
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]

/-- Splitting the coefficient sum at a distinguished composition isolates the
    all-ones branch while preserving the concrete composition terms. -/
private theorem finiteTaylorJet_comp_topCoeff_branch_split
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) +
        ∑ c : Composition m, if c = Composition.ones m then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
  classical
  rw [finiteTaylorJet_comp_topCoeff_branch_sum]
  have hsingle :
      (∑ c : Composition m, if c = Composition.ones m then
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c else 0) =
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) := by
    rw [Finset.sum_ite_eq']
    simp
  calc
    (∑ c : Composition m,
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c) =
        ∑ c : Composition m,
          ((if c = Composition.ones m then
              Q.toFormalMultilinearSeries.compAlongComposition
                P.toFormalMultilinearSeries c else 0) +
            (if c = Composition.ones m then 0 else
              Q.toFormalMultilinearSeries.compAlongComposition
                P.toFormalMultilinearSeries c)) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : c = Composition.ones m
      · simp [h]
      · simp [h]
    _ = (∑ c : Composition m, if c = Composition.ones m then
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c else 0) +
        ∑ c : Composition m, if c = Composition.ones m then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
      rw [Finset.sum_add_distrib]
    _ = Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) +
        ∑ c : Composition m, if c = Composition.ones m then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
      rw [hsingle]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): the
outer coefficient selected by the all-one composition is the top finite-jet
coefficient. -/
private theorem finiteTaylorJet_norm_formalSub_onesLength
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} (Q R : FiniteTaylorJet ℝ E F m) :
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
        (Composition.ones m).length‖ =
      ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
        R.coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  rw [Composition.ones_length]
  change
    ‖Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m‖ = _
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): the
inner factors selected by the all-one composition multiply to the `m`-th
power of the linear finite-jet coefficient norm. -/
private theorem finiteTaylorJet_norm_formal_onesProduct
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} (hm : 0 < m) (P : FiniteTaylorJet ℝ E F m) :
    ∏ i, ‖P.toFormalMultilinearSeries
        ((Composition.ones m).blocksFun i)‖ =
      ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
  classical
  calc
    ∏ i, ‖P.toFormalMultilinearSeries
        ((Composition.ones m).blocksFun i)‖ =
        ∏ _i : Fin (Composition.ones m).length,
          ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Composition.ones_blocksFun,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))]
    _ = ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
      simp only [Finset.prod_const, Finset.card_fin, Composition.ones_length]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): the
top coefficient variation through a fixed inner jet is controlled by the top
outer variation and the `m`-th power of the inner linear coefficient. -/
private theorem finiteTaylorJet_norm_comp_topCoeff_sub_le_outer
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (hm : 0 < m) (Q R : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < m → Q.coeff k = R.coeff k) :
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
  rw [finiteTaylorJet_comp_topCoeff_sub_eq_outer Q R P hQR]
  calc
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m)‖ ≤
        ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
            (Composition.ones m).length‖ *
          ∏ i, ‖P.toFormalMultilinearSeries
            ((Composition.ones m).blocksFun i)‖ :=
      FormalMultilinearSeries.compAlongComposition_norm _ _ _
    _ = ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
      rw [finiteTaylorJet_norm_formalSub_onesLength,
        finiteTaylorJet_norm_formal_onesProduct hm]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): a
coefficient of a finite-jet composition is unchanged when the needed outer
coefficients and positive inner coefficients agree through that order. -/
private theorem finiteTaylorJet_comp_coeff_eq_of_eq_below
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q R : FiniteTaylorJet ℝ F G m)
    (P S : FiniteTaylorJet ℝ E F m) (n : Fin (m + 1))
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) ≤ (n : ℕ) → Q.coeff k = R.coeff k)
    (hPS : ∀ k : Fin (m + 1), 0 < (k : ℕ) → (k : ℕ) ≤ (n : ℕ) →
      P.coeff k = S.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff n =
      (FiniteTaylorJet.comp R S).coeff n := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp]
  apply Finset.sum_congr rfl
  intro c _
  ext z
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  have hlengthBound : c.length ≤ (n : ℕ) := c.length_le
  have hlengthOrder : c.length ≤ m :=
    hlengthBound.trans (Nat.le_of_lt_succ n.isLt)
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hlengthOrder,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R hlengthOrder,
    hQR ⟨c.length, hlengthBound.trans_lt n.isLt⟩ hlengthBound]
  congr 1
  funext i
  dsimp only [FormalMultilinearSeries.applyComposition]
  have hblockBound : c.blocksFun i ≤ (n : ℕ) :=
    c.blocksFun_le i
  have hblockOrder : c.blocksFun i ≤ m :=
    hblockBound.trans (Nat.le_of_lt_succ n.isLt)
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hblockOrder,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le S hblockOrder,
    hPS ⟨c.blocksFun i, hblockBound.trans_lt n.isLt⟩
      (c.one_le_blocksFun i) hblockBound]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): at a
fixed center coordinate, the stable output of the cutoff map is Lipschitz in
the fiber with constant `linearRate + stableFiber`. -/
private theorem stableOutput_lipschitzWith (u : ℝ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (linearRate stableCenter stableFiber : ℝ≥0)
    (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_lipschitz : ∀ a b : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (a, z)).2 -
          (LocalCutoff.remainder χ ρ N (b, w)).2‖ ≤
        (stableCenter : ℝ) * |a - b| + (stableFiber : ℝ) * ‖z - w‖) :
    LipschitzWith (linearRate + stableFiber)
      (fun z ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, z)).2) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hout (x : X) :
      (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2 =
        L x + (LocalCutoff.remainder χ ρ N (u, x)).2 := by
    rw [LocalCutoff.centerStableLinearize_apply, LocalCutoff.centerStable_apply]
    change L x + (χ (ρ⁻¹ • (u, x)) • N (u, x)).2 = _
    rw [LocalCutoff.remainder_apply]
  have hlinear : ‖L z - L w‖ ≤ (linearRate : ℝ) * ‖z - w‖ := by
    rw [← map_sub]
    exact (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have hstable := h_stable_lipschitz u u z w
  simp only [sub_self, abs_zero, mul_zero, zero_add] at hstable
  rw [dist_eq_norm, hout z, hout w]
  calc
    ‖(L z + (LocalCutoff.remainder χ ρ N (u, z)).2) -
        (L w + (LocalCutoff.remainder χ ρ N (u, w)).2)‖ =
        ‖(L z - L w) + ((LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (u, w)).2)‖ := by
      congr 1
      abel
    _ ≤ ‖L z - L w‖ +
        ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (u, w)).2‖ := norm_add_le _ _
    _ ≤ (linearRate : ℝ) * ‖z - w‖ +
        (stableFiber : ℝ) * ‖z - w‖ := add_le_add hlinear hstable
    _ = ((linearRate + stableFiber : ℝ≥0) : ℝ) * dist z w := by
      simp only [NNReal.coe_add, dist_eq_norm]
      ring

/-- If lower-order coefficients agree, the differentiated graph transform
contracts the top order by `rate * lower⁻¹ ^ r`. -/
theorem topCoeff_contraction (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hr_pos : 1 ≤ r) (hrν : r ≤ ν)
    (hχ_smooth : ContDiff ℝ ν χ) (hχ_support : HasCompactSupport χ)
    (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_linearRate : linearRate < 1)
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_center_fiber : ∀ u : ℝ, ∀ z w : X,
      |(LocalCutoff.remainder χ ρ N (u, z)).1 -
          (LocalCutoff.remainder χ ρ N (u, w)).1| ≤
        (centerFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (h_rate : rate lower linearRate stableCenter stableFiber centerFiber slope < 1)
    (h_bunching : rate lower linearRate stableCenter stableFiber centerFiber slope *
      lower⁻¹ ^ r < 1)
    (J K : BoundedGraphJet X radius slope r)
    (h_lower_coeff : ∀ u (n : Fin (r + 1)), (n : ℕ) < r →
      (J.jet u).coeff n = (K.jet u).coeff n) :
    coeffDistance ⟨r, Nat.lt_succ_self r⟩
      (map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
        hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero
        hL h_stable_bound h_stable_lipschitz h_radius h_slope J)
      (map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
        hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero
        hL h_stable_bound h_stable_lipschitz h_radius h_slope K) ≤
      (rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r : ℝ≥0) *
        coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K := by
  have hzero_lt : (0 : ℕ) < r := by
    omega
  have hgraph : J.graph = K.graph := by
    ext u
    have hcoeff := h_lower_coeff u (0 : Fin (r + 1)) hzero_lt
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] X ↦ A (fun _ ↦ 0)) hcoeff
    calc
      J.graph u = (J.jet u).constantCoeff := (J.constantCoeff_eq u).symm
      _ = (J.jet u).coeff (0 : Fin (r + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero (J.jet u)
      _ = (K.jet u).coeff (0 : Fin (r + 1)) (fun _ ↦ 0) := hcoeffValue
      _ = (K.jet u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero (K.jet u)).symm
      _ = K.graph u := K.constantCoeff_eq u
  have hparamCoeff (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (graphParametrizationJet r J u).coeff n =
        (graphParametrizationJet r K u).coeff n := by
    rw [graphParametrizationJet, graphParametrizationJet,
      FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod,
      h_lower_coeff u n hn]
  have hparamConstant (u : ℝ) :
      (graphParametrizationJet r J u).constantCoeff =
        (graphParametrizationJet r K u).constantCoeff := by
    have hcoeff := hparamCoeff u (0 : Fin (r + 1)) hzero_lt
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (graphParametrizationJet r J u).constantCoeff =
          (graphParametrizationJet r J u).coeff (0 : Fin (r + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (graphParametrizationJet r K u).coeff
          (0 : Fin (r + 1)) (fun _ ↦ 0) := hcoeffValue
      _ = (graphParametrizationJet r K u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  have himageCoeff (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (imageJet r χ ρ L N J u).coeff n =
        (imageJet r χ ρ L N K u).coeff n := by
    rw [imageJet, imageJet, FiniteTaylorJet.postcomp_def,
      FiniteTaylorJet.postcomp_def, hparamConstant u]
    apply JetTransform.finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro k _
      rfl
    · intro k _ hk
      exact hparamCoeff u k (hk.trans_lt hn)
  have himageConstant (u : ℝ) :
      (imageJet r χ ρ L N J u).constantCoeff =
        (imageJet r χ ρ L N K u).constantCoeff := by
    have hcoeff := himageCoeff u (0 : Fin (r + 1)) hzero_lt
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (imageJet r χ ρ L N J u).constantCoeff =
          (imageJet r χ ρ L N J u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (imageJet r χ ρ L N K u).coeff
          (0 : Fin (r + 1)) (fun _ ↦ 0) := hcoeffValue
      _ = (imageJet r χ ρ L N K u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  have hstableCoeff (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (stableJet r χ ρ L N J u).coeff n =
        (stableJet r χ ρ L N K u).coeff n := by
    rw [stableJet, stableJet, FiniteTaylorJet.postcomp_def,
      FiniteTaylorJet.postcomp_def, himageConstant u]
    apply JetTransform.finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro k _
      rfl
    · intro k _ hk
      exact himageCoeff u k (hk.trans_lt hn)
  have hparamTopValue (u : ℝ) (z : Fin r → ℝ) :
      ((graphParametrizationJet r J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (graphParametrizationJet r K u).coeff ⟨r, Nat.lt_succ_self r⟩) z =
        (0, ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z) := by
    rw [graphParametrizationJet, graphParametrizationJet,
      FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod]
    change
      ((FiniteTaylorJet.ofFunction ℝ r id u).coeff ⟨r, Nat.lt_succ_self r⟩ z -
          (FiniteTaylorJet.ofFunction ℝ r id u).coeff ⟨r, Nat.lt_succ_self r⟩ z,
        (J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ z -
          (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ z) = _
    rw [sub_self]
    rfl
  have himageTop (u : ℝ) :
      (imageJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (imageJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩ =
        (continuousMultilinearCurryFin1 ℝ (ℝ × X) (ℝ × X)
          ((FiniteTaylorJet.ofFunction ℝ r
            (LocalCutoff.centerStableLinearize χ ρ L N)
              (graphParametrizationJet r J u).constantCoeff).coeff
                ⟨1, Nat.succ_lt_succ hzero_lt⟩)).compContinuousMultilinearMap
          ((graphParametrizationJet r J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (graphParametrizationJet r K u).coeff ⟨r, Nat.lt_succ_self r⟩) := by
    rw [imageJet, imageJet, FiniteTaylorJet.postcomp_def,
      FiniteTaylorJet.postcomp_def, hparamConstant u]
    exact finiteTaylorJet_comp_topCoeff_sub_eq_inner hzero_lt _ _ _
      (hparamCoeff u)
  have hstableTop (u : ℝ) :
      (stableJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (stableJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩ =
        (continuousMultilinearCurryFin1 ℝ (ℝ × X) X
          ((FiniteTaylorJet.ofFunction ℝ r Prod.snd
            (imageJet r χ ρ L N J u).constantCoeff).coeff
              ⟨1, Nat.succ_lt_succ hzero_lt⟩)).compContinuousMultilinearMap
          ((imageJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (imageJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩) := by
    rw [stableJet, stableJet, FiniteTaylorJet.postcomp_def,
      FiniteTaylorJet.postcomp_def, himageConstant u]
    exact finiteTaylorJet_comp_topCoeff_sub_eq_inner hzero_lt _ _ _
      (himageCoeff u)
  have hparamBase (u : ℝ) :
      (graphParametrizationJet r J u).constantCoeff = (u, J.graph u) := by
    rw [graphParametrizationJet, finiteTaylorJet_constantCoeff_prod,
      FiniteTaylorJet.constantCoeff_ofFunction, J.constantCoeff_eq]
    rfl
  have hstableTopValue (u : ℝ) (z : Fin r → ℝ) :
      ((stableJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (stableJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩) z =
        (fderiv ℝ (LocalCutoff.centerStableLinearize χ ρ L N)
          (u, J.graph u)
            (0, ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
              (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z)).2 := by
    rw [hstableTop u, ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply, himageTop u,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      hparamTopValue u z, hparamBase u]
    rw [continuousMultilinearCurryFin1_apply,
      FiniteTaylorJet.coeff_ofFunction_apply]
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_one_apply, fderiv_snd, ContinuousLinearMap.coe_snd',
      Fin.snoc_zero]
    rw [continuousMultilinearCurryFin1_apply,
      FiniteTaylorJet.coeff_ofFunction_apply]
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_one_apply, fderiv_snd, ContinuousLinearMap.coe_snd',
      Fin.snoc_zero]
  have hcutoffSmooth : ContDiff ℝ ν (fun p : ℝ × X ↦ χ (ρ⁻¹ • p)) :=
    hχ_smooth.comp (contDiff_const_smul ρ⁻¹)
  have hremainderEq : LocalCutoff.remainder χ ρ N =
      (fun p : ℝ × X ↦ χ (ρ⁻¹ • p)) • N := by
    funext p
    exact LocalCutoff.remainder_apply χ ρ N p
  have hremainderSmooth : ContDiff ℝ ν (LocalCutoff.remainder χ ρ N) := by
    rw [hremainderEq]
    exact hcutoffSmooth.smul hN_smooth
  have hlinearizeEq : LocalCutoff.centerStableLinearize χ ρ L N =
      LocalCutoff.centerStable L + LocalCutoff.remainder χ ρ N := by
    funext p
    rw [Pi.add_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.remainder_apply]
  have hlinearizeSmooth :
      ContDiff ℝ ν (LocalCutoff.centerStableLinearize χ ρ L N) := by
    rw [hlinearizeEq]
    exact (LocalCutoff.centerStable L).contDiff.add hremainderSmooth
  have hν_ne : ν ≠ 0 := by
    omega
  have hν_cast_ne : (ν : WithTop ENat) ≠ 0 := Nat.cast_ne_zero.mpr hν_ne
  have hlinearizeDifferentiable :
      Differentiable ℝ (LocalCutoff.centerStableLinearize χ ρ L N) :=
    hlinearizeSmooth.differentiable hν_cast_ne
  have hstableOutputDifferentiable : Differentiable ℝ
      (fun p : ℝ × X ↦ (LocalCutoff.centerStableLinearize χ ρ L N p).2) :=
    hlinearizeDifferentiable.snd
  have hstableOutputFDeriv (p : ℝ × X) :
      fderiv ℝ (fun q : ℝ × X ↦
          (LocalCutoff.centerStableLinearize χ ρ L N q).2) p =
        (ContinuousLinearMap.snd ℝ ℝ X).comp
          (fderiv ℝ (LocalCutoff.centerStableLinearize χ ρ L N) p) :=
    fderiv.snd (hlinearizeDifferentiable p)
  have hsliceFDeriv (u : ℝ) :
      fderiv ℝ
          (fun x : X ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2)
            (J.graph u) =
        (fderiv ℝ (fun p : ℝ × X ↦
          (LocalCutoff.centerStableLinearize χ ρ L N p).2) (u, J.graph u)).comp
            (ContinuousLinearMap.inr ℝ ℝ X) := by
    have hcomp := (hstableOutputDifferentiable (u, J.graph u)).hasFDerivAt.comp
      (J.graph u) (hasFDerivAt_prodMk_right u (J.graph u))
    have hsliceEq :
        (fun x : X ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2) =
          (fun p : ℝ × X ↦
            (LocalCutoff.centerStableLinearize χ ρ L N p).2) ∘ Prod.mk u := by
      rfl
    rw [hsliceEq]
    exact hcomp.fderiv
  have hstableTopSliceValue (u : ℝ) (z : Fin r → ℝ) :
      ((stableJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (stableJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩) z =
        fderiv ℝ
          (fun x : X ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2)
            (J.graph u)
              (((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
                (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z) := by
    rw [hstableTopValue u z, hsliceFDeriv u, hstableOutputFDeriv]
    rfl
  have hstableTopNorm (u : ℝ) :
      ‖(stableJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (stableJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩‖ ≤
        ((linearRate + stableFiber : ℝ≥0) : ℝ) *
          ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖ := by
    have hsliceNorm :
        ‖fderiv ℝ
          (fun x : X ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2)
            (J.graph u)‖ ≤ ((linearRate + stableFiber : ℝ≥0) : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ
        (stableOutput_lipschitzWith u χ ρ L N linearRate stableCenter stableFiber hL
          h_stable_lipschitz)
    apply ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (linearRate + stableFiber).coe_nonneg (norm_nonneg _))
    intro z
    rw [hstableTopSliceValue u z]
    calc
      ‖fderiv ℝ
          (fun x : X ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2)
            (J.graph u)
              (((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
                (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z)‖ ≤
          ‖fderiv ℝ
            (fun x : X ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2)
              (J.graph u)‖ *
            ‖((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
              (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z‖ :=
        (fderiv ℝ
          (fun x : X ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, x)).2)
            (J.graph u)).le_opNorm _
      _ ≤ ((linearRate + stableFiber : ℝ≥0) : ℝ) *
          ‖((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z‖ :=
        mul_le_mul_of_nonneg_right hsliceNorm (norm_nonneg _)
      _ ≤ (((linearRate + stableFiber : ℝ≥0) : ℝ) *
          ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖) *
          ∏ i, ‖z i‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          ((ContinuousMultilinearMap.le_opNorm
            ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
              (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z))
          (linearRate + stableFiber).coe_nonneg
  have hone_le_ν : 1 ≤ ν := by
    omega
  have hone_le_ν_cast : (1 : WithTop ENat) ≤ (ν : WithTop ENat) := by
    exact_mod_cast hone_le_ν
  have hinverseCoeffOneNorm (u : ℝ) :
      ‖(FiniteTaylorJet.ofFunction ℝ r
        (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) u).coeff
          ⟨1, Nat.succ_lt_succ hzero_lt⟩‖ ≤ (lower⁻¹ : ℝ≥0) := by
    rw [FiniteTaylorJet.coeff_ofFunction]
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      LocalCutoff.CenterProjection.inverse_def]
    exact Real.norm_iteratedDeriv_one_invFun_le
      ((h_center_smooth J.graph).of_le hone_le_ν_cast) h_lower_pos
        (h_lower J.graph) u
  have hdifferentiatedCoeff (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (differentiatedJet r χ ρ L N J u).coeff n =
        (differentiatedJet r χ ρ L N K u).coeff n := by
    rw [differentiatedJet, differentiatedJet, hgraph]
    apply finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro k hk
      exact hstableCoeff _ k (hk.trans_lt hn)
    · intro k _ _
      rfl
  have hdifferentiatedTopNorm (u : ℝ) :
      ‖(differentiatedJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (differentiatedJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩‖ ≤
        (((linearRate + stableFiber) * lower⁻¹ ^ r : ℝ≥0) : ℝ) *
          ‖(J.jet (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u)).coeff
              ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u)).coeff
              ⟨r, Nat.lt_succ_self r⟩‖ := by
    rw [differentiatedJet, differentiatedJet, ← hgraph]
    let u₀ := LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u
    let inverseJet := FiniteTaylorJet.ofFunction ℝ r
      (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) u
    calc
      ‖(FiniteTaylorJet.comp (stableJet r χ ρ L N J u₀) inverseJet).coeff
            ⟨r, Nat.lt_succ_self r⟩ -
          (FiniteTaylorJet.comp (stableJet r χ ρ L N K u₀) inverseJet).coeff
            ⟨r, Nat.lt_succ_self r⟩‖ ≤
          ‖(stableJet r χ ρ L N J u₀).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (stableJet r χ ρ L N K u₀).coeff ⟨r, Nat.lt_succ_self r⟩‖ *
              ‖inverseJet.coeff ⟨1, Nat.succ_lt_succ hzero_lt⟩‖ ^ r :=
        finiteTaylorJet_norm_comp_topCoeff_sub_le_outer hzero_lt _ _ _
          (hstableCoeff u₀)
      _ ≤ (((linearRate + stableFiber : ℝ≥0) : ℝ) *
          ‖(J.jet u₀).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u₀).coeff ⟨r, Nat.lt_succ_self r⟩‖) *
              ((lower⁻¹ : ℝ≥0) : ℝ) ^ r := by
        gcongr
        · exact hstableTopNorm u₀
        · exact hinverseCoeffOneNorm u
      _ = (((linearRate + stableFiber) * lower⁻¹ ^ r : ℝ≥0) : ℝ) *
          ‖(J.jet u₀).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u₀).coeff ⟨r, Nat.lt_succ_self r⟩‖ := by
        simp only [NNReal.coe_mul, NNReal.coe_pow]
        ring
  have hinputBdd : BddAbove (Set.range fun u ↦
      ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
        (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖) := by
    refine ⟨(J.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ) +
      (K.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ), ?_⟩
    rintro _ ⟨u, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add
      (J.coeff_le u ⟨r, Nat.lt_succ_self r⟩)
      (K.coeff_le u ⟨r, Nat.lt_succ_self r⟩))
  have hinputLe (u : ℝ) :
      ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖ ≤
        coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K := by
    exact le_csSup hinputBdd ⟨u, rfl⟩
  have hdirectRate :
      (linearRate + stableFiber) * lower⁻¹ ^ r ≤
        rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r := by
    gcongr
    rw [rate_def]
    have hextraNonneg : 0 ≤
        (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ * centerFiber := by
      positivity
    exact le_add_of_nonneg_right hextraNonneg
  have hdirectRateReal :
      (((linearRate + stableFiber) * lower⁻¹ ^ r : ℝ≥0) : ℝ) ≤
        ((rate lower linearRate stableCenter stableFiber centerFiber slope *
          lower⁻¹ ^ r : ℝ≥0) : ℝ) := by
    exact_mod_cast hdirectRate
  rw [coeffDistance]
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨u, rfl⟩
    change
      ‖(differentiatedJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (differentiatedJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩‖ ≤
        ((rate lower linearRate stableCenter stableFiber centerFiber slope *
          lower⁻¹ ^ r : ℝ≥0) : ℝ) *
            sSup (Set.range fun v ↦
              ‖(J.jet v).coeff ⟨r, Nat.lt_succ_self r⟩ -
                (K.jet v).coeff ⟨r, Nat.lt_succ_self r⟩‖)
    calc
      ‖(differentiatedJet r χ ρ L N J u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (differentiatedJet r χ ρ L N K u).coeff ⟨r, Nat.lt_succ_self r⟩‖ ≤
        (((linearRate + stableFiber) * lower⁻¹ ^ r : ℝ≥0) : ℝ) *
          ‖(J.jet (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u)).coeff
              ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u)).coeff
              ⟨r, Nat.lt_succ_self r⟩‖ := hdifferentiatedTopNorm u
      _ ≤ ((rate lower linearRate stableCenter stableFiber centerFiber slope *
          lower⁻¹ ^ r : ℝ≥0) : ℝ) *
          ‖(J.jet (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u)).coeff
              ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u)).coeff
              ⟨r, Nat.lt_succ_self r⟩‖ :=
        mul_le_mul_of_nonneg_right hdirectRateReal (norm_nonneg _)
      _ ≤ ((rate lower linearRate stableCenter stableFiber centerFiber slope *
          lower⁻¹ ^ r : ℝ≥0) : ℝ) *
            sSup (Set.range fun v ↦
              ‖(J.jet v).coeff ⟨r, Nat.lt_succ_self r⟩ -
                (K.jet v).coeff ⟨r, Nat.lt_succ_self r⟩‖) :=
        mul_le_mul_of_nonneg_left
          (hinputLe (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u))
          (rate lower linearRate stableCenter stableFiber centerFiber slope *
            lower⁻¹ ^ r).coe_nonneg

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): the differentiated
construction has coefficientwise lower-order congruence through its jet stages. -/
private theorem differentiatedJet_coeff_congr_of_lower
    {m : ℕ} (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J K : BoundedGraphJet X radius slope m)
    (hgraph : J.graph = K.graph)
    (h_lower_coeff : ∀ u (k : Fin (m + 1)), (k : ℕ) < m →
      (J.jet u).coeff k = (K.jet u).coeff k)
    (n : Fin (m + 1)) (hn : (n : ℕ) < m) (ū : ℝ) :
    (differentiatedJet m χ ρ L N J ū).coeff n =
      (differentiatedJet m χ ρ L N K ū).coeff n := by
  classical
  have hm_pos : 0 < m := by omega
  have hparamCoeff (u : ℝ) (k : Fin (m + 1)) (hk : (k : ℕ) ≤ (n : ℕ)) :
      (graphParametrizationJet m J u).coeff k =
        (graphParametrizationJet m K u).coeff k := by
    rw [graphParametrizationJet, graphParametrizationJet,
      FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod]
    rw [h_lower_coeff u k (lt_of_le_of_lt hk hn)]
  have hparamConstant (u : ℝ) :
      (graphParametrizationJet m J u).constantCoeff =
        (graphParametrizationJet m K u).constantCoeff := by
    have hcoeff := hparamCoeff u (0 : Fin (m + 1)) (Nat.zero_le _)
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (graphParametrizationJet m J u).constantCoeff =
          (graphParametrizationJet m J u).coeff (0 : Fin (m + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (graphParametrizationJet m K u).coeff (0 : Fin (m + 1)) (fun _ ↦ 0) :=
        hcoeffValue
      _ = (graphParametrizationJet m K u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  have himageCoeff (u : ℝ) (k : Fin (m + 1)) (hk : (k : ℕ) ≤ (n : ℕ)) :
      (imageJet m χ ρ L N J u).coeff k =
        (imageJet m χ ρ L N K u).coeff k := by
    rw [imageJet, imageJet, FiniteTaylorJet.postcomp_def,
      FiniteTaylorJet.postcomp_def, hparamConstant u]
    apply finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro j _
      rfl
    · intro j hj_pos hj_le
      exact hparamCoeff u j (hj_le.trans hk)
  have himageConstant (u : ℝ) :
      (imageJet m χ ρ L N J u).constantCoeff =
        (imageJet m χ ρ L N K u).constantCoeff := by
    have hcoeff := himageCoeff u (0 : Fin (m + 1)) (Nat.zero_le _)
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (imageJet m χ ρ L N J u).constantCoeff =
          (imageJet m χ ρ L N J u).coeff (0 : Fin (m + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (imageJet m χ ρ L N K u).coeff (0 : Fin (m + 1)) (fun _ ↦ 0) :=
        hcoeffValue
      _ = (imageJet m χ ρ L N K u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  have hstableCoeff (u : ℝ) (k : Fin (m + 1)) (hk : (k : ℕ) ≤ (n : ℕ)) :
      (stableJet m χ ρ L N J u).coeff k =
        (stableJet m χ ρ L N K u).coeff k := by
    rw [stableJet, stableJet, FiniteTaylorJet.postcomp_def,
      FiniteTaylorJet.postcomp_def, himageConstant u]
    apply finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro j _
      rfl
    · intro j hj_pos hj_le
      exact himageCoeff u j (hj_le.trans hk)
  rw [differentiatedJet, differentiatedJet, hgraph]
  apply JetTransform.finiteTaylorJet_comp_coeff_eq_of_eq_below
  · intro k hk
    exact hstableCoeff _ k hk
  · intro k _ _
    rfl

end JetTransform

/-- A Taylor-update adapter for Infrastructure I.16 (Finite-order graph-jet
contraction) replaces only the top coefficient of a successor witness. -/
private theorem updateTaylorSeriesSuccTop
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F}
    (hp : HasFTaylorSeriesUpTo n f p)
    (a : E → (E [×(n + 1)]→L[ℝ] F)) (ha : Continuous a)
    (hderiv : ∀ x, HasFDerivAt (fun y ↦ p y n) ((a x).curryLeft) x) :
    HasFTaylorSeriesUpTo (n + 1) f
      (fun x ↦ Function.update (p x) (n + 1) (a x)) := by
  -- Name the updated series once so all coefficient cases use the same normal form.
  let q : E → FormalMultilinearSeries ℝ E F :=
    fun x ↦ Function.update (p x) (n + 1) (a x)
  have hzero : ∀ x, (q x 0).curry0 = f x := by
    intro x
    dsimp only [q]
    rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ n + 1)]
    exact hp.zero_eq x
  have hderiv_below : ∀ m : ℕ, m < n + 1 → ∀ x,
      HasFDerivAt (fun y ↦ q y m) (q x m.succ).curryLeft x := by
    intro m hm x
    by_cases htop : m = n
    · subst m
      have hq_prev : (fun y ↦ q y n) = fun y ↦ p y n := by
        funext y
        dsimp only [q]
        rw [Function.update_of_ne (by omega : n ≠ n + 1)]
      have hq_top : q x n.succ = a x := by
        dsimp only [q]
        rw [Function.update_self]
      rw [hq_prev, hq_top]
      exact hderiv x
    · have hbelow : m < n := by omega
      have hp_deriv := hp.fderiv m (by exact_mod_cast hbelow) x
      have hq_m : (fun y ↦ q y m) = fun y ↦ p y m := by
        funext y
        dsimp only [q]
        rw [Function.update_of_ne (by omega : m ≠ n + 1)]
      have hq_succ : q x m.succ = p x m.succ := by
        dsimp only [q]
        rw [Function.update_of_ne (by omega : m.succ ≠ n + 1)]
      rw [hq_m, hq_succ]
      exact hp_deriv
  have hcont : ∀ m : ℕ, m ≤ n + 1 → Continuous (q · m) := by
    intro m hm
    by_cases htop : m = n + 1
    · subst m
      simpa only [q, Function.update_self] using ha
    · have hbelow : m ≤ n := by omega
      have hp_cont := hp.cont m (by exact_mod_cast hbelow)
      have hq_m : (q · m) = (p · m) := by
        funext y
        dsimp only [q]
        rw [Function.update_of_ne (by omega : m ≠ n + 1)]
      rw [hq_m]
      exact hp_cont
  have hseries : HasFTaylorSeriesUpTo (n + 1) f q := by
    refine ⟨hzero, ?_, ?_⟩
    · intro m hm x
      exact hderiv_below m (by exact_mod_cast hm) x
    · intro m hm
      exact hcont m (by exact_mod_cast hm)
  simpa only [q] using hseries

/-- A first-order little-o remainder at a translated base point determines the
Fréchet derivative at that point. -/
private theorem hasFDerivAt_of_isLittleO_shift
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : ℝ → Y) (u : ℝ) (A : ℝ →L[ℝ] Y)
    (h : (fun h : ℝ => p (u + h) - p u - A h) =o[𝓝 0] (fun h : ℝ => h)) :
    HasFDerivAt p A u := by
  -- Translate the remainder to the origin, where the standard derivative
  -- characterization applies directly.
  have hg : HasFDerivAt (fun h : ℝ => p (u + h)) A 0 := by
    apply (hasFDerivAt_iff_isLittleO_nhds_zero (f := fun h : ℝ => p (u + h))
      (f' := A) (x := 0)).mpr
    simpa only [zero_add, add_zero, sub_zero] using h
  -- Compose with the inverse affine translation and normalize its linear map.
  have htranslate : HasFDerivAt (fun y : ℝ => y - u)
      (ContinuousLinearMap.id ℝ ℝ) u := by
    simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) u).sub_const u
  have hg' : HasFDerivAt (fun h : ℝ => p (u + h)) A (u - u) := by
    simpa only [sub_self] using hg
  have hcomp : HasFDerivAt ((fun h : ℝ => p (u + h)) ∘ (fun y : ℝ => y - u))
      (A.comp (ContinuousLinearMap.id ℝ ℝ)) u := by
    apply HasFDerivAt.comp u
    · simpa only [sub_self] using hg'
    · exact htranslate
  have hA : A.comp (ContinuousLinearMap.id ℝ ℝ) = A := by
    ext y
    simp
  rw [hA] at hcomp
  change HasFDerivAt (fun y : ℝ => p (u + (y - u))) A u at hcomp
  -- The translated function agrees everywhere with the original one.
  exact hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by
      congr 1
      ring)

/-- Helper for Infrastructure I.16: a strict contraction absorbs a lower-order
remainder in a norm inequality. -/
private theorem isLittleO_of_norm_le_mul_self_add
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {R e : ℝ → Y} {q : ℝ} (hq : q < 1)
    (hineq : ∀ᶠ h in 𝓝 0, ‖R h‖ ≤ q * ‖R h‖ + ‖e h‖)
    (he : e =o[𝓝 0] (fun h : ℝ ↦ h)) :
    R =o[𝓝 0] (fun h : ℝ ↦ h) := by
  -- Reserve the strict contraction gap for the prescribed little-o scale.
  rw [isLittleO_iff]
  intro ε hε
  have hgap : 0 < (1 - q) * ε :=
    mul_pos (sub_pos.mpr hq) hε
  filter_upwards [hineq, (isLittleO_iff.mp he hgap)] with h hR heh
  -- Absorb the self-term, then divide by the positive contraction gap.
  have habsorbed : (1 - q) * ‖R h‖ ≤ ‖e h‖ := by
    nlinarith
  nlinarith [norm_nonneg (R h), norm_nonneg h]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): an
eventual scalar contraction inequality transfers convergence of its additive
error to the nonnegative residual. -/
private theorem tendsto_zero_of_le_mul_self_add
    {R e : ℝ → ℝ} {q : ℝ} (hq : q < 1)
    (hR : ∀ t, 0 ≤ R t)
    (hineq : ∀ᶠ t in 𝓝 0, R t ≤ q * R t + e t)
    (he : Tendsto e (𝓝 0) (𝓝 0)) :
    Tendsto R (𝓝 0) (𝓝 0) := by
  -- Divide the absorbed inequality by the positive contraction gap.
  have hgap : 0 < 1 - q := sub_pos.mpr hq
  have hupper : ∀ᶠ t in 𝓝 0, R t ≤ e t / (1 - q) := by
    filter_upwards [hineq] with t ht
    apply (le_div_iff₀ hgap).mpr
    nlinarith
  -- The rescaled error tends to zero, so the residual is squeezed to zero.
  apply squeeze_zero' (Filter.Eventually.of_forall hR) hupper
  simpa only [zero_div] using he.div_const (1 - q)

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): a
little-o estimate against the constant unit scale is convergence to zero. -/
private theorem tendsto_zero_of_isLittleO_const_one
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} (hf : f =o[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ))) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  -- The little-o estimate is exactly the metric epsilon condition after
  -- normalizing the constant comparison function.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  filter_upwards [isLittleO_iff.mp hf hhalf] with t ht
  have hnorm : ‖f t‖ < ε := by
    calc
      ‖f t‖ ≤ ε / 2 * ‖(1 : ℝ)‖ := ht
      _ < ε := by simp only [norm_one]; linarith
  simpa only [dist_zero_right] using hnorm

/-- Helper for Infrastructure I.16: a differentiable map with uniformly
continuous Fréchet derivative has a first-order Taylor remainder controlled
uniformly over all base points. -/
private theorem uniformFirstOrderRemainder_of_uniformContinuous_fderiv
    {E : Type v} {Y : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : E → Y} (hf : Differentiable ℝ f)
    (hderiv : UniformContinuous (fderiv ℝ f))
    {C : ℝ} (hC : 0 < C) :
    ∃ δ > 0, ∀ x h : E, ‖h‖ < δ →
      ‖f (x + h) - f x - fderiv ℝ f x h‖ ≤ C * ‖h‖ := by
  obtain ⟨δ, hδ, hmodulus⟩ :=
    Metric.uniformContinuous_iff.mp hderiv C hC
  refine ⟨δ, hδ, ?_⟩
  intro x h hh
  let p : E := x
  let q : E := x + h
  let A : E →L[ℝ] Y := fderiv ℝ f p
  let g : E → Y := fun z ↦ f z - A z
  have hpq : q - p = h := by
    simp only [q, p, add_sub_cancel_left]
  have hpq_dist : dist p q < δ := by
    rw [dist_comm, dist_eq_norm, hpq]
    exact hh
  have hderivative_bound : ∀ z ∈ segment ℝ p q,
      ‖fderiv ℝ f z - A‖ ≤ C := by
    intro z hz
    have hzp_norm : ‖z - p‖ ≤ ‖q - p‖ :=
      norm_sub_le_of_mem_segment hz
    have hpq_norm_lt : ‖q - p‖ < δ := by
      simpa only [dist_comm p q, dist_eq_norm] using hpq_dist
    have hzp_dist : dist z p < δ := by
      rw [dist_eq_norm]
      exact hzp_norm.trans_lt hpq_norm_lt
    have hclose := hmodulus hzp_dist
    simpa only [A, p, dist_eq_norm] using hclose.le
  have hg_derivative : ∀ z ∈ segment ℝ p q,
      HasFDerivWithinAt g (fderiv ℝ f z - A) (segment ℝ p q) z := by
    intro z _hz
    exact ((hf z).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt
  have hmean :=
    (convex_segment p q).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hg_derivative hderivative_bound
      (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  have hA_difference : A q - A p = A h := by
    rw [← map_sub, hpq]
  have hg_algebra : g q - g p = f q - f p - (A q - A p) := by
    dsimp only [g]
    abel
  simpa only [hg_algebra, hA_difference, hpq, q, p, A] using hmean

/-- Helper for Infrastructure I.16: a derivative-built finite-jet coefficient
is `C¹` whenever the source map has one more derivative than that coefficient. -/
private theorem contDiffOne_ofFunction_coeff_of_succ_le
    {E : Type v} {Y : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m q : ℕ} (f : E → Y) (hf : ContDiff ℝ q f)
    (n : Fin (m + 1)) (hn : 1 + (n : ℕ) ≤ q) :
    ContDiff ℝ 1
      (fun x : E ↦ (FiniteTaylorJet.ofFunction ℝ m f x).coeff n) := by
  have hcoefficient_eq :
      (fun x : E ↦ (FiniteTaylorJet.ofFunction ℝ m f x).coeff n) =
        fun x ↦ ((n : ℕ).factorial : ℝ)⁻¹ •
          iteratedFDeriv ℝ (n : ℕ) f x := by
    funext x
    exact FiniteTaylorJet.coeff_ofFunction m f x n
  rw [hcoefficient_eq]
  have horder :
      (1 : WithTop ENat) + ((n : ℕ) : WithTop ENat) ≤
        (q : WithTop ENat) := by
    exact_mod_cast hn
  have hderivative :
      ContDiff ℝ 1 (iteratedFDeriv ℝ (n : ℕ) f) :=
    hf.iteratedFDeriv_right horder
  have hconstant :
      ContDiff ℝ 1 (fun _ : E ↦ ((n : ℕ).factorial : ℝ)⁻¹) :=
    contDiff_const
  exact hconstant.smul hderivative

/-- Helper for Infrastructure I.16: coefficientwise `C¹` scalar-source jets
remain coefficientwise `C¹` after taking their product. -/
private theorem contDiffOne_prod_coeff
    {E : Type v} {Y : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (P : ℝ → FiniteTaylorJet ℝ ℝ E m)
    (Q : ℝ → FiniteTaylorJet ℝ ℝ Y m)
    (hP : ∀ n : Fin (m + 1), ContDiff ℝ 1 (fun x ↦ (P x).coeff n))
    (hQ : ∀ n : Fin (m + 1), ContDiff ℝ 1 (fun x ↦ (Q x).coeff n))
    (n : Fin (m + 1)) :
    ContDiff ℝ 1 (fun x ↦ (FiniteTaylorJet.prod (P x) (Q x)).coeff n) := by
  have hcoefficient_eq :
      (fun x ↦ (FiniteTaylorJet.prod (P x) (Q x)).coeff n) =
        fun x ↦ (P x).coeff n |>.prod ((Q x).coeff n) := by
    funext x
    exact FiniteTaylorJet.coeff_prod (P x) (Q x) n
  rw [hcoefficient_eq]
  exact (ContinuousMultilinearMap.prodL ℝ
    (fun _ : Fin (n : ℕ) ↦ ℝ) E Y).contDiff.comp
      ((hP n).prodMk (hQ n))

/-- Helper for Infrastructure I.16: coefficientwise `C¹` scalar-source jets
remain coefficientwise `C¹` after composition when the intermediate and
target spaces lie in independent universes. -/
private theorem contDiffOne_comp_coeff_universes
    {F : Type v} {G : Type w}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : ℕ}
    (P : ℝ → FiniteTaylorJet ℝ ℝ F m)
    (Q : ℝ → FiniteTaylorJet ℝ F G m)
    (hP : ∀ n : Fin (m + 1), ContDiff ℝ 1 (fun u ↦ (P u).coeff n))
    (hQ : ∀ n : Fin (m + 1), ContDiff ℝ 1 (fun u ↦ (Q u).coeff n))
    (n : Fin (m + 1)) :
    ContDiff ℝ 1 (fun u ↦ (FiniteTaylorJet.comp (Q u) (P u)).coeff n) := by
  apply FiniteTaylorJet.contDiffOne_multilinearMap_of_apply_one
  simp only [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp,
    _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
  apply ContDiff.sum
  intro c hc
  have hlengthOrder : c.length ≤ m :=
    c.length_le.trans (Nat.le_of_lt_succ n.isLt)
  have houter : ContDiff ℝ 1
      (fun u ↦ (Q u).toFormalMultilinearSeries c.length) := by
    have houter_eq :
        (fun u ↦ (Q u).toFormalMultilinearSeries c.length) =
          fun u ↦ (Q u).coeff
            ⟨c.length, Nat.lt_succ_iff.mpr hlengthOrder⟩ := by
      funext u
      exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
        (Q u) hlengthOrder
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
      exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
        (P u) hblockOrder
    rw [hinner_eq]
    exact hP _
  have hinner_apply (i : Fin c.length) : ContDiff ℝ 1 (fun u ↦
      (P u).toFormalMultilinearSeries (c.blocksFun i)
        (fun _ ↦ (1 : ℝ))) := by
    let evaluator :
        (ℝ [×c.blocksFun i]→L[ℝ] F) →L[ℝ] F :=
      ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin (c.blocksFun i) ↦ ℝ) F (fun _ ↦ (1 : ℝ))
    have hevaluated := evaluator.contDiff.comp (hinner i)
    simpa only [Function.comp_def, evaluator,
      ContinuousMultilinearMap.apply_apply] using hevaluated
  have hevaluation : ContDiff ℝ 1 (fun p :
      (F [×c.length]→L[ℝ] G) × (Fin c.length → F) ↦ p.1 p.2) := by
    rw [← contDiffOn_univ]
    apply AnalyticOn.contDiffOn
      (ContinuousLinearMap.analyticOn_uncurry_of_multilinear
        (f := ContinuousLinearMap.id ℝ (F [×c.length]→L[ℝ] G)))
      uniqueDiffOn_univ
  have harguments : ContDiff ℝ 1 (fun u ↦
      ((Q u).toFormalMultilinearSeries c.length,
        fun i ↦ (P u).toFormalMultilinearSeries (c.blocksFun i)
          (fun _ ↦ (1 : ℝ)))) := by
    apply ContDiff.prodMk
    · exact houter
    · apply contDiff_pi.2
      intro i
      exact hinner_apply i
  exact hevaluation.comp harguments

/-- The first-order secant remainder of a translated `C¹` function is uniform
on every compact set of translation centers. -/
private theorem translatedSecantUniformRemainderOn
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} (hf : ContDiff ℝ 1 f) {K : Set ℝ} (hK : IsCompact K)
    {C : ℝ} (hC : 0 < C) :
    ∃ δ > 0, ∀ u ∈ K, ∀ h : ℝ, ‖h‖ < δ →
      ‖(FiniteTaylorJet.ofFunction ℝ 1 (fun z : ℝ ↦ f (u + z)) 0).remainder
        (fun z : ℝ ↦ f (u + z)) 0 h‖ ≤ C * ‖h‖ := by
  -- Apply the joint compact-fiber Taylor theorem to the translated family.
  let g : ℝ → ℝ → Y := fun u h ↦ f (u + h)
  have hg : ContDiff ℝ 1 (Function.uncurry g) := by
    have hg' : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) :=
      hf.comp (contDiff_fst.add contDiff_snd)
    convert hg' using 1
    funext p
    rfl
  have huniform := FiniteTaylorJet.uniformRemainderOn_of_contDiff
    1 g 0 K hK hg C hC
  obtain ⟨δ, hδ, hbound⟩ := FiniteTaylorJet.IsUniformRemainderOn.bound huniform
  refine ⟨δ, hδ, ?_⟩
  intro u hu h hh
  simpa [g, pow_one] using hbound u hu h hh

/-- A pointwise bound on bounded-continuous sections is a bound in the
    supremum metric. -/
private theorem boundedContinuousFunction_dist_le_of_pointwise
    {Y : Type*} [PseudoMetricSpace Y]
    (f g : BoundedContinuousFunction ℝ Y) (C : ℝ)
    (h : ∀ u, dist (f u) (g u) ≤ C) : dist f g ≤ C := by
  exact BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr h

/-- Coefficients of scalar-source finite compositions vary continuously in the
    base parameter, with independent universes for the scalar and stable targets.
    This is used by the Infrastructure I.16 graph-jet contraction estimate. -/
private theorem continuousScalarCompositionCoeff
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (P : ℝ → FiniteTaylorJet ℝ ℝ ℝ m)
    (Q : ℝ → FiniteTaylorJet ℝ ℝ G m)
    (hP : ∀ n : Fin (m + 1), Continuous (fun u ↦ (P u).coeff n))
    (hQ : ∀ n : Fin (m + 1), Continuous (fun u ↦ (Q u).coeff n))
    (n : Fin (m + 1)) :
    Continuous (fun u ↦ (FiniteTaylorJet.comp (Q u) (P u)).coeff n) := by
  have hcontinuous_of_apply_one {k : ℕ}
      (f : ℝ → (ℝ [×k]→L[ℝ] G))
      (hf : Continuous (fun u ↦ f u (fun _ ↦ 1))) : Continuous f := by
    have hfactor : f = fun u ↦
        ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) G
          (f u (fun _ ↦ 1)) := by
      funext u
      exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) G).apply_symm_apply
        (f u) |>.symm
    rw [hfactor]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) G).continuous.comp hf
  apply hcontinuous_of_apply_one
  simp only [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp,
    _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
  apply continuous_finsetSum
  intro c _
  have hlengthOrder : c.length ≤ m :=
    c.length_le.trans (Nat.le_of_lt_succ n.isLt)
  have houter : Continuous (fun u ↦ (Q u).toFormalMultilinearSeries c.length) := by
    have houter_eq : (fun u ↦ (Q u).toFormalMultilinearSeries c.length) =
        fun u ↦ (Q u).coeff ⟨c.length, Nat.lt_succ_iff.mpr hlengthOrder⟩ := by
      funext u
      exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le (Q u) hlengthOrder
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
      exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le (P u) hblockOrder
    rw [hinner_eq]
    exact hP _
  have hinner_apply (i : Fin c.length) : Continuous (fun u ↦
      (P u).toFormalMultilinearSeries (c.blocksFun i) (fun _ ↦ (1 : ℝ))) :=
    (hinner i).eval continuous_const
  exact houter.eval (continuous_pi hinner_apply)

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): finite
    branch estimates can be assembled before taking a supremum over the base
    parameter. -/
private theorem finiteComposition_nonOnes_uniformBound
    {α Y : Type*} [Fintype α] [DecidableEq α] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y]
    (distinguished : α) (b : α → ℝ → Y) (C : α → ℝ)
    (hbranch : ∀ c, ∀ᶠ t in 𝓝 0,
      c ≠ distinguished → ‖b c t‖ ≤ C c * ‖t‖) :
    ∀ᶠ t in 𝓝 0,
      ‖∑ c : α, if c = distinguished then 0 else b c t‖ ≤
        (∑ c : α, if c = distinguished then 0 else C c) * ‖t‖ := by
  classical
  have hAll : ∀ᶠ t in 𝓝 0, ∀ c, c ≠ distinguished →
      ‖b c t‖ ≤ C c * ‖t‖ :=
    (Filter.eventually_all).mpr hbranch
  -- Apply the norm triangle inequality and sum the branchwise estimates.
  filter_upwards [hAll] with t ht
  calc
    ‖∑ c : α, if c = distinguished then 0 else b c t‖ ≤
        ∑ c : α, ‖if c = distinguished then 0 else b c t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : α, (if c = distinguished then 0 else C c) * ‖t‖ := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hcd : c = distinguished
      · simp [hcd]
      · simpa [hcd] using ht c hcd
    _ = (∑ c : α, if c = distinguished then 0 else C c) * ‖t‖ := by
      rw [Finset.sum_mul]

/-- A finite family of compact-uniform linear branch bounds has one common
    radius, and the corresponding non-distinguished sum obeys the summed
    bound. -/
private theorem finiteComposition_nonOnes_uniformBoundOn
    {α Θ Y : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (distinguished : α) (K : Set Θ) (b : α → Θ → ℝ → Y) (C : α → ℝ)
    (hbranch : ∀ c, c ≠ distinguished → ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
      ‖t‖ < δ → ‖b c u t‖ ≤ C c * ‖t‖) :
    ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : α, if c = distinguished then 0 else b c u t‖ ≤
        (∑ c : α, if c = distinguished then 0 else C c) * ‖t‖ := by
  classical
  have hbranch_eventually (c : α) (hc : c ≠ distinguished) :
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u ∈ K, ‖b c u t‖ ≤ C c * ‖t‖ := by
    obtain ⟨δ, hδ, hδ_spec⟩ := hbranch c hc
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, ?_⟩
    intro t ht u hu
    exact hδ_spec u hu t (by simpa only [dist_zero_right] using ht)
  have hbranch_eventually' (c : α) :
      ∀ᶠ t in 𝓝 (0 : ℝ), c ≠ distinguished →
        ∀ u ∈ K, ‖b c u t‖ ≤ C c * ‖t‖ := by
    by_cases hc : c = distinguished
    · filter_upwards [] with t hct
      exact (hct hc).elim
    · simpa [hc] using hbranch_eventually c hc
  have hAll : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ c, c ≠ distinguished →
      ∀ u ∈ K, ‖b c u t‖ ≤ C c * ‖t‖ :=
    (Filter.eventually_all).mpr hbranch_eventually'
  obtain ⟨δ, hδ, hδ_spec⟩ := (Metric.eventually_nhds_iff.mp hAll)
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  have hbranches : ∀ c, c ≠ distinguished →
      ‖b c u t‖ ≤ C c * ‖t‖ := by
    intro c hc
    exact hδ_spec (by simpa only [dist_zero_right] using ht) c hc u hu
  calc
    ‖∑ c : α, if c = distinguished then 0 else b c u t‖ ≤
        ∑ c : α, ‖if c = distinguished then 0 else b c u t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : α, (if c = distinguished then 0 else C c) * ‖t‖ := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hcd : c = distinguished
      · simp [hcd]
      · simpa [hcd] using hbranches c hcd
    _ = (∑ c : α, if c = distinguished then 0 else C c) * ‖t‖ := by
      rw [Finset.sum_mul]

/-- A finite family of branch terms that vanish uniformly on a parameter set has
    a common radius on which the filtered sum also vanishes uniformly. -/
private theorem finiteFamilyNonOnesUniformVanishingOn
    {α Θ Y : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (distinguished : α) (K : Set Θ) (b : α → Θ → ℝ → Y)
    (hbranch : ∀ c, c ≠ distinguished → ∀ η > 0, ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
      ‖t‖ < δ → ‖b c u t‖ < η) :
    ∀ η > 0, ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : α, if c = distinguished then 0 else b c u t‖ < η := by
  classical
  intro η hη
  let share : ℝ := η / ((Fintype.card α : ℝ) + 1)
  have hcard_pos : 0 < (Fintype.card α : ℝ) + 1 := by positivity
  have hshare_pos : 0 < share := by
    dsimp only [share]
    exact div_pos hη hcard_pos
  have hbranch_eventually (c : α) : ∀ᶠ t in 𝓝 (0 : ℝ),
      c ≠ distinguished → ∀ u ∈ K, ‖b c u t‖ < share := by
    by_cases hc : c = distinguished
    · filter_upwards [] with t hct
      exact (hct hc).elim
    · obtain ⟨δ, hδ, hδ_spec⟩ := hbranch c hc share hshare_pos
      rw [Metric.eventually_nhds_iff]
      refine ⟨δ, hδ, ?_⟩
      intro t ht _hc' u hu
      exact hδ_spec u hu t (by simpa only [dist_zero_right] using ht)
  have hAll : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ c, c ≠ distinguished →
      ∀ u ∈ K, ‖b c u t‖ < share :=
    (Filter.eventually_all).mpr hbranch_eventually
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.eventually_nhds_iff.mp hAll
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  have hbranches : ∀ c, c ≠ distinguished → ‖b c u t‖ < share := by
    intro c hc
    exact hδ_spec (by simpa only [dist_zero_right] using ht) c hc u hu
  calc
    ‖∑ c : α, if c = distinguished then 0 else b c u t‖ ≤
        ∑ c : α, ‖if c = distinguished then 0 else b c u t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : α, share := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hcd : c = distinguished
      · simp [hcd, hshare_pos.le]
      · simpa [hcd] using (hbranches c hcd).le
    _ = (Fintype.card α : ℝ) * share := by simp
    _ < η := by
      have hcard_lt : (Fintype.card α : ℝ) < (Fintype.card α : ℝ) + 1 := by norm_num
      calc
        (Fintype.card α : ℝ) * share <
            ((Fintype.card α : ℝ) + 1) * share :=
          mul_lt_mul_of_pos_right hcard_lt hshare_pos
        _ = η := by
          dsimp only [share]
          field_simp

/-- Helper for Infrastructure I.16: a finite family of branch terms that are
    individually little-o remains little-o after removing one distinguished
    branch. -/
private theorem finiteComposition_nonOnes_uniformLittleO
    {α Y : Type*} [Fintype α] [DecidableEq α] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y]
    (distinguished : α) (b : α → ℝ → Y)
    (hbranch : ∀ c, c ≠ distinguished →
      (fun t ↦ b c t) =o[𝓝 0] (fun t : ℝ ↦ t)) :
    (fun t ↦ ∑ c : α, if c = distinguished then 0 else b c t) =o[𝓝 0]
      (fun t : ℝ ↦ t) := by
  classical
  let A : α → ℝ → Y := fun c t ↦ if c = distinguished then 0 else b c t
  have hA : ∀ c, A c =o[𝓝 0] (fun t : ℝ ↦ t) := by
    intro c
    by_cases hc : c = distinguished
    · simpa only [A, hc, if_pos] using (isLittleO_zero (fun t : ℝ ↦ t) (𝓝 0))
    · simpa only [A, hc, if_false] using hbranch c hc
  have hsum := Asymptotics.IsLittleO.sum
    (s := (Finset.univ : Finset α)) (fun c _ ↦ hA c)
  simpa [A] using hsum

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): the
    inverse-reindexed increment is carried exactly by a bijective center map. -/
private theorem inverseCenter_reindexedIncrement_spec
    {f : ℝ → ℝ} (hf : Function.Bijective f) (u t : ℝ) (ht : t ≠ 0) :
    f (u + (Function.invFun f (f u + t) - u)) = f u + t ∧
      Function.invFun f (f u) = u ∧
        Function.invFun f (f u + t) - u ≠ 0 := by
  -- Cancel the inverse at the base point and normalize the transported endpoint.
  have hleft : Function.invFun f (f u) = u :=
    Function.leftInverse_invFun hf.1 u
  have harg : u + (Function.invFun f (f u + t) - u) =
      Function.invFun f (f u + t) := by
    rw [← hleft]
    ring
  -- The right-inverse identity gives the forward transport; injectivity then
  -- rules out a zero transported increment when the target increment is nonzero.
  refine ⟨?_, hleft, ?_⟩
  · rw [harg]
    exact Function.rightInverse_invFun hf.2 (f u + t)
  · intro hzero
    have hinv : Function.invFun f (f u + t) = u := sub_eq_zero.mp hzero
    have hsum : f u + t = f u := by
      calc
        f u + t = f (Function.invFun f (f u + t)) :=
          (Function.rightInverse_invFun hf.2 (f u + t)).symm
        _ = f u := by rw [hinv]
    exact ht (by linarith [hsum])

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): an
    output-coordinate increment pulls back to the corresponding source
    increment under a bijective center map. -/
private theorem outputReindexedSecant_spec
    {Y : Type*} [NormedAddCommGroup Y]
    {f : ℝ → ℝ} (hf : Function.Bijective f) (p : ℝ → Y) (u h : ℝ) :
    Function.invFun f (f u + (f (u + h) - f u)) - Function.invFun f (f u) = h ∧
      p (Function.invFun f (f u + (f (u + h) - f u))) -
          p (Function.invFun f (f u)) = p (u + h) - p u := by
  -- Normalize the forward endpoint and cancel both inverse evaluations.
  have hsum : f u + (f (u + h) - f u) = f (u + h) := by ring
  have hleft_u : Function.invFun f (f u) = u :=
    Function.leftInverse_invFun hf.1 u
  have hleft_uh : Function.invFun f (f (u + h)) = u + h :=
    Function.leftInverse_invFun hf.1 (u + h)
  constructor
  · rw [hsum, hleft_uh, hleft_u]
    ring
  · rw [hsum, hleft_uh, hleft_u]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): a
    nonzero source increment remains nonzero after applying an injective center
    map. -/
private theorem outputReindexedIncrement_ne
    {f : ℝ → ℝ} (hf : Function.Bijective f) (u h : ℝ) (hh : h ≠ 0) :
    f (u + h) - f u ≠ 0 := by
  intro hzero
  have hforward : f (u + h) = f u := sub_eq_zero.mp hzero
  -- The first component of a bijection is already an injective function.
  have hsource : u + h = u := hf.1 hforward
  exact hh (by linarith [hsource])

/-- Helper for Infrastructure I.16: the all-ones composition is the outer
   coefficient at its length applied to repeated first inner coefficients. -/
private theorem finiteTaylorJet_comp_topCoeff_outer_ones_apply
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q R : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m) (x : E) :
    ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m)) (fun _ : Fin m ↦ x) =
      (Q.toFormalMultilinearSeries (Composition.ones m).length -
        R.toFormalMultilinearSeries (Composition.ones m).length)
        (fun _ : Fin (Composition.ones m).length ↦
          P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x)) := by
  -- Expand the composition application and normalize its all-ones blocks.
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  rw [FormalMultilinearSeries.applyComposition_ones]
  rfl

/-- The only composition of order one is the all-ones composition.  This
    boundary fact lets the finite-branch argument separate the `r = 1` case
    before invoking lower-order secant estimates. -/
private theorem composition_order_one_eq_ones (c : Composition 1) :
    c = Composition.ones 1 := by
  apply Composition.eq_ones_iff_length.mpr
  have hpos : 0 < c.length := c.length_pos_of_pos (by norm_num)
  exact Nat.le_antisymm c.length_le (by omega)

/-- Helper for Infrastructure I.16: the finite jet obtained by setting only
the top coefficient to zero. -/
private noncomputable def truncateTopCoeff
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} (Q : FiniteTaylorJet ℝ E F m) : FiniteTaylorJet ℝ E F m :=
  FiniteTaylorJet.replaceTopCoeff Q 0

/-- Helper for Infrastructure I.16: top truncation identifies finite jets whose
coefficients agree below the top order. -/
private theorem truncateTopCoeff_eq_of_coeff_eq_below
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} (Q R : FiniteTaylorJet ℝ E F m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < m → Q.coeff k = R.coeff k) :
    truncateTopCoeff Q = truncateTopCoeff R := by
  apply FiniteTaylorJet.ext_coeff
  intro k
  by_cases hk : (k : ℕ) < m
  · unfold truncateTopCoeff
    rw [FiniteTaylorJet.replaceTopCoeff_coeff_of_lt Q 0 k hk,
      FiniteTaylorJet.replaceTopCoeff_coeff_of_lt R 0 k hk]
    exact hQR k hk
  · have hktop : k = ⟨m, Nat.lt_succ_self m⟩ := by
      apply Fin.ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt) (Nat.le_of_not_gt hk)
    subst k
    unfold truncateTopCoeff
    rw [FiniteTaylorJet.replaceTopCoeff_coeff_top,
      FiniteTaylorJet.replaceTopCoeff_coeff_top]

/-- Helper for Infrastructure I.16: the full predecessor jet transported
through a stable map and a scalar inverse parametrization. -/
private noncomputable def nestedEndpointJet
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (m : ℕ) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (y : ℝ) : FiniteTaylorJet ℝ ℝ Y m :=
  FiniteTaylorJet.comp
    (FiniteTaylorJet.comp
      (FiniteTaylorJet.ofFunction ℝ m stable
        (inverse y, graph (inverse y)))
      (FiniteTaylorJet.prod
        (FiniteTaylorJet.ofFunction ℝ m id (inverse y))
        (FiniteTaylorJet.ofFunction ℝ m graph (inverse y))))
    (FiniteTaylorJet.ofFunction ℝ m inverse y)

/-- Helper for Infrastructure I.16: the zero-top predecessor jet transported
through a stable map and a scalar inverse parametrization. -/
private noncomputable def truncatedNestedEndpointJet
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (m : ℕ) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (y : ℝ) : FiniteTaylorJet ℝ ℝ Y m :=
  FiniteTaylorJet.comp
    (FiniteTaylorJet.comp
      (FiniteTaylorJet.ofFunction ℝ m stable
        (inverse y, graph (inverse y)))
      (FiniteTaylorJet.prod
        (FiniteTaylorJet.ofFunction ℝ m id (inverse y))
        (truncateTopCoeff
          (FiniteTaylorJet.ofFunction ℝ m graph (inverse y)))))
    (FiniteTaylorJet.ofFunction ℝ m inverse y)

/-- Helper for Infrastructure I.16: every coefficient of the zero-top nested
endpoint is `C¹` when the inverse and stable map have one derivative beyond
the predecessor order. -/
private theorem contDiffOne_truncatedNestedEndpointJet_coeff
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (hinverse : ContDiff ℝ (m + 1) inverse)
    (hgraph : ContDiff ℝ m graph) (hstable : ContDiff ℝ (m + 1) stable)
    (n : Fin (m + 1)) :
    ContDiff ℝ 1 (fun y ↦
      (truncatedNestedEndpointJet m inverse graph stable y).coeff n) := by
  have hinverse_one : ContDiff ℝ 1 inverse := by
    apply hinverse.of_le
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
  have hgraph_one : ContDiff ℝ 1 graph := by
    apply hgraph.of_le
    exact_mod_cast hm
  let scalarJet : ℝ → FiniteTaylorJet ℝ ℝ ℝ m := fun y ↦
    FiniteTaylorJet.ofFunction ℝ m id (inverse y)
  let flatGraphJet : ℝ → FiniteTaylorJet ℝ ℝ X m := fun y ↦
    truncateTopCoeff
      (FiniteTaylorJet.ofFunction ℝ m graph (inverse y))
  let graphJet : ℝ → FiniteTaylorJet ℝ ℝ (ℝ × X) m := fun y ↦
    FiniteTaylorJet.prod (scalarJet y) (flatGraphJet y)
  let stableOuterJet : ℝ → FiniteTaylorJet ℝ (ℝ × X) Y m := fun y ↦
    FiniteTaylorJet.ofFunction ℝ m stable
      (inverse y, graph (inverse y))
  let stableEndpointJet : ℝ → FiniteTaylorJet ℝ ℝ Y m := fun y ↦
    FiniteTaylorJet.comp (stableOuterJet y) (graphJet y)
  let inverseJet : ℝ → FiniteTaylorJet ℝ ℝ ℝ m := fun y ↦
    FiniteTaylorJet.ofFunction ℝ m inverse y
  have hid_smooth : ContDiff ℝ (m + 1) (id : ℝ → ℝ) := contDiff_id
  have hscalarJet_coeff (k : Fin (m + 1)) :
      ContDiff ℝ 1 (fun y ↦ (scalarJet y).coeff k) := by
    have hk : 1 + (k : ℕ) ≤ m + 1 := by omega
    have hcoefficient := contDiffOne_ofFunction_coeff_of_succ_le
      (id : ℝ → ℝ) hid_smooth k hk
    exact hcoefficient.comp hinverse_one
  have hflatGraphJet_coeff (k : Fin (m + 1)) :
      ContDiff ℝ 1 (fun y ↦ (flatGraphJet y).coeff k) := by
    by_cases hk : (k : ℕ) < m
    · have hcoefficient_eq :
          (fun y ↦ (flatGraphJet y).coeff k) = fun y ↦
            (FiniteTaylorJet.ofFunction ℝ m graph (inverse y)).coeff k := by
        funext y
        dsimp only [flatGraphJet, truncateTopCoeff]
        rw [FiniteTaylorJet.replaceTopCoeff_coeff_of_lt _ 0 k hk]
      rw [hcoefficient_eq]
      have hk_order : 1 + (k : ℕ) ≤ m := by omega
      have hcoefficient := contDiffOne_ofFunction_coeff_of_succ_le
        graph hgraph k hk_order
      exact hcoefficient.comp hinverse_one
    · have htop_val : (k : ℕ) = m := by omega
      have htop : k = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext htop_val
      subst k
      simp only [flatGraphJet, truncateTopCoeff,
        FiniteTaylorJet.replaceTopCoeff_coeff_top]
      exact contDiff_const
  have hgraphJet_coeff (k : Fin (m + 1)) :
      ContDiff ℝ 1 (fun y ↦ (graphJet y).coeff k) := by
    exact contDiffOne_prod_coeff scalarJet flatGraphJet
      hscalarJet_coeff hflatGraphJet_coeff k
  have hbase : ContDiff ℝ 1 (fun y ↦
      (inverse y, graph (inverse y))) :=
    hinverse_one.prodMk (hgraph_one.comp hinverse_one)
  have hstableOuterJet_coeff (k : Fin (m + 1)) :
      ContDiff ℝ 1 (fun y ↦ (stableOuterJet y).coeff k) := by
    have hk : 1 + (k : ℕ) ≤ m + 1 := by omega
    have hcoefficient := contDiffOne_ofFunction_coeff_of_succ_le
      stable hstable k hk
    exact hcoefficient.comp hbase
  have hstableEndpointJet_coeff (k : Fin (m + 1)) :
      ContDiff ℝ 1 (fun y ↦ (stableEndpointJet y).coeff k) := by
    exact contDiffOne_comp_coeff_universes graphJet stableOuterJet
      hgraphJet_coeff hstableOuterJet_coeff k
  have hinverseJet_coeff (k : Fin (m + 1)) :
      ContDiff ℝ 1 (fun y ↦ (inverseJet y).coeff k) := by
    have hk : 1 + (k : ℕ) ≤ m + 1 := by omega
    exact contDiffOne_ofFunction_coeff_of_succ_le inverse hinverse k hk
  have hfinal := contDiffOne_comp_coeff_universes
    inverseJet stableEndpointJet hinverseJet_coeff
      hstableEndpointJet_coeff n
  simpa only [truncatedNestedEndpointJet, scalarJet, flatGraphJet, graphJet,
    stableOuterJet, stableEndpointJet, inverseJet] using hfinal

/-- Helper for Infrastructure I.16: the predecessor cocycle's principal
operator is the stable fiber derivative scaled by the repeated first inverse
coefficient. -/
private noncomputable def nestedPrincipalOperator
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (m : ℕ) (hm : 0 < m) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (y : ℝ) : X →L[ℝ] Y :=
  (((FiniteTaylorJet.ofFunction ℝ m inverse y).coeff
      ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ (1 : ℝ))) ^ m) •
    (fderiv ℝ stable (inverse y, graph (inverse y))).comp
      (ContinuousLinearMap.inr ℝ ℝ X)

/-- Helper for Infrastructure I.16: the predecessor principal operator is
`C¹` when the inverse and stable map are `C²` and the graph is `C¹`. -/
private theorem contDiffOne_nestedPrincipalOperator
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (hinverse : ContDiff ℝ (m + 1) inverse)
    (hgraph : ContDiff ℝ m graph) (hstable : ContDiff ℝ (m + 1) stable) :
    ContDiff ℝ 1
      (nestedPrincipalOperator m hm inverse graph stable) := by
  have hinverse_one : ContDiff ℝ 1 inverse := by
    apply hinverse.of_le
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
  have hgraph_one : ContDiff ℝ 1 graph := by
    apply hgraph.of_le
    exact_mod_cast hm
  have hfirst_order : 1 + (1 : ℕ) ≤ m + 1 := by omega
  have hfirstCoefficient : ContDiff ℝ 1 (fun y ↦
      (FiniteTaylorJet.ofFunction ℝ m inverse y).coeff
        ⟨1, Nat.succ_lt_succ hm⟩) :=
    contDiffOne_ofFunction_coeff_of_succ_le inverse hinverse
      ⟨1, Nat.succ_lt_succ hm⟩ hfirst_order
  let evaluator : (ℝ [×1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ ℝ) ℝ
      (fun _ ↦ (1 : ℝ))
  have hfirst : ContDiff ℝ 1 (fun y ↦
      (FiniteTaylorJet.ofFunction ℝ m inverse y).coeff
        ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ (1 : ℝ))) := by
    have hevaluated := evaluator.contDiff.comp hfirstCoefficient
    simpa only [Function.comp_def, evaluator,
      ContinuousMultilinearMap.apply_apply] using hevaluated
  have hderivative_order :
      (1 : WithTop ENat) + 1 ≤ ((m + 1 : ℕ) : WithTop ENat) := by
    exact_mod_cast hfirst_order
  have hstable_fderiv : ContDiff ℝ 1 (fderiv ℝ stable) :=
    hstable.fderiv_right hderivative_order
  have hbase : ContDiff ℝ 1 (fun y ↦
      (inverse y, graph (inverse y))) :=
    hinverse_one.prodMk (hgraph_one.comp hinverse_one)
  have hstable_fderiv_base : ContDiff ℝ 1 (fun y ↦
      fderiv ℝ stable (inverse y, graph (inverse y))) :=
    hstable_fderiv.comp hbase
  have hinr : ContDiff ℝ 1
      (fun _ : ℝ ↦ ContinuousLinearMap.inr ℝ ℝ X) := contDiff_const
  have hfiber : ContDiff ℝ 1 (fun y ↦
      (fderiv ℝ stable (inverse y, graph (inverse y))).comp
        (ContinuousLinearMap.inr ℝ ℝ X)) :=
    hstable_fderiv_base.clm_comp hinr
  have hoperator_eq :
      nestedPrincipalOperator m hm inverse graph stable = fun y ↦
        (((FiniteTaylorJet.ofFunction ℝ m inverse y).coeff
          ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ (1 : ℝ))) ^ m) •
          (fderiv ℝ stable (inverse y, graph (inverse y))).comp
            (ContinuousLinearMap.inr ℝ ℝ X) := rfl
  rw [hoperator_eq]
  exact (hfirst.pow m).smul hfiber

/-- Helper for Infrastructure I.16: composing a product jet twice is affine in
the top coefficient of its fiber component, with the center component fixed. -/
private theorem finiteTaylorJet_comp_prod_truncateTop_topCoeff_affine
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet ℝ (ℝ × X) Y m)
    (C : FiniteTaylorJet ℝ ℝ ℝ m)
    (P : FiniteTaylorJet ℝ ℝ X m)
    (I : FiniteTaylorJet ℝ ℝ ℝ m) :
    let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let oneM : Fin m → ℝ := fun _ ↦ 1
    let oneI : Fin 1 → ℝ := fun _ ↦ 1
    (((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff top -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q
            (FiniteTaylorJet.prod C (truncateTopCoeff P))) I).coeff top) oneM) =
      ((I.coeff ⟨1, Nat.succ_lt_succ hm⟩ oneI) ^ m) •
        (continuousMultilinearCurryFin1 ℝ (ℝ × X) Y
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
            (0, P.coeff top oneM) := by
  have hlower (k : Fin (m + 1)) (hk : (k : ℕ) < m) :
      P.coeff k = (FiniteTaylorJet.replaceTopCoeff P 0).coeff k := by
    exact (FiniteTaylorJet.replaceTopCoeff_coeff_of_lt P 0 k hk).symm
  have htop :
      (FiniteTaylorJet.replaceTopCoeff P 0).coeff
          ⟨m, Nat.lt_succ_self m⟩ = 0 := by
    exact FiniteTaylorJet.replaceTopCoeff_coeff_top P 0
  simpa only [truncateTopCoeff] using
    FiniteTaylorJet.comp_prod_comp_topCoeff_sub_eq_inner_of_zeroTop
      hm Q C P (FiniteTaylorJet.replaceTopCoeff P 0) I hlower htop

/-- Helper for Infrastructure I.16: removing the predecessor top coefficient
from a nested endpoint leaves exactly the principal operator applied to that
coefficient at the repeated-one vector. -/
private theorem nestedEndpointJet_topCoeff_sub_truncated_apply
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (y : ℝ) :
    (((nestedEndpointJet m inverse graph stable y).coeff
          ⟨m, Nat.lt_succ_self m⟩ -
        (truncatedNestedEndpointJet m inverse graph stable y).coeff
          ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ (1 : ℝ))) =
      nestedPrincipalOperator m hm inverse graph stable y
        ((FiniteTaylorJet.ofFunction ℝ m graph (inverse y)).coeff
          ⟨m, Nat.lt_succ_self m⟩
          (fun _ : Fin m ↦ (1 : ℝ))) := by
  have hsplit := finiteTaylorJet_comp_prod_truncateTop_topCoeff_affine hm
    (FiniteTaylorJet.ofFunction ℝ m stable
      (inverse y, graph (inverse y)))
    (FiniteTaylorJet.ofFunction ℝ m id (inverse y))
    (FiniteTaylorJet.ofFunction ℝ m graph (inverse y))
    (FiniteTaylorJet.ofFunction ℝ m inverse y)
  have houterFirstCoefficient :
      (FiniteTaylorJet.ofFunction ℝ m stable
          (inverse y, graph (inverse y))).coeff
          ⟨1, Nat.succ_lt_succ hm⟩
          (Fin.snoc 0
            (0, (FiniteTaylorJet.ofFunction ℝ m graph (inverse y)).coeff
              ⟨m, Nat.lt_succ_self m⟩
              (fun _ : Fin m ↦ (1 : ℝ)))) =
        (fderiv ℝ stable (inverse y, graph (inverse y))).comp
          (ContinuousLinearMap.inr ℝ ℝ X)
          ((FiniteTaylorJet.ofFunction ℝ m graph (inverse y)).coeff
            ⟨m, Nat.lt_succ_self m⟩
            (fun _ : Fin m ↦ (1 : ℝ))) := by
    rw [FiniteTaylorJet.coeff_ofFunction_apply]
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_one_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, Fin.snoc_zero]
  simpa only [nestedEndpointJet, truncatedNestedEndpointJet,
    nestedPrincipalOperator, FiniteTaylorJet.coeff_ofFunction_apply,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_one_apply, continuousMultilinearCurryFin1_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    houterFirstCoefficient, ContinuousLinearMap.smul_apply] using hsplit

/-- Helper for Infrastructure I.16: the lower-order forcing is the
factorial-normalized repeated-one value of the zero-top nested endpoint. -/
private noncomputable def nestedEndpointForcing
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (m : ℕ) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (y : ℝ) : Y :=
  (m.factorial : ℝ) •
    ((truncatedNestedEndpointJet m inverse graph stable y).coeff
      ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ (1 : ℝ)))

/-- Helper for Infrastructure I.16: the zero-top nested-endpoint forcing is
`C¹` under the predecessor-order regularity budget. -/
private theorem contDiffOne_nestedEndpointForcing
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (hinverse : ContDiff ℝ (m + 1) inverse)
    (hgraph : ContDiff ℝ m graph) (hstable : ContDiff ℝ (m + 1) stable) :
    ContDiff ℝ 1 (nestedEndpointForcing m inverse graph stable) := by
  let evaluator : (ℝ [×m]→L[ℝ] Y) →L[ℝ] Y :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ ℝ) Y
      (fun _ ↦ (1 : ℝ))
  have hcoefficient := contDiffOne_truncatedNestedEndpointJet_coeff hm
    inverse graph stable hinverse hgraph hstable
      ⟨m, Nat.lt_succ_self m⟩
  have hevaluated := evaluator.contDiff.comp hcoefficient
  have hforcing_eq :
      nestedEndpointForcing m inverse graph stable = fun x ↦
        (m.factorial : ℝ) •
          ((truncatedNestedEndpointJet m inverse graph stable x).coeff
            ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ (1 : ℝ))) := rfl
  rw [hforcing_eq]
  simpa only [evaluator, Function.comp_def,
    ContinuousMultilinearMap.apply_apply] using
      (ContDiff.const_smul (m.factorial : ℝ) hevaluated)

/-- Helper for Infrastructure I.16: the principal predecessor operator in
source coordinates is obtained by composing its output-coordinate value with
the forward center map. -/
private noncomputable def sourceNestedPrincipalOperator
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (m : ℕ) (hm : 0 < m) (inverse forward : ℝ → ℝ)
    (graph : ℝ → X) (stable : ℝ × X → Y) (x : ℝ) : X →L[ℝ] Y :=
  nestedPrincipalOperator m hm inverse graph stable (forward x)

/-- Helper for Infrastructure I.16: the zero-top predecessor forcing in source
coordinates is obtained by composing with the forward center map. -/
private noncomputable def sourceNestedEndpointForcing
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (m : ℕ) (inverse forward : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → Y) (x : ℝ) : Y :=
  nestedEndpointForcing m inverse graph stable (forward x)

/-- Helper for Infrastructure I.16: the source-coordinate principal operator
and forcing are `C¹` whenever the forward center map is `C¹`. -/
private theorem contDiffOne_sourceNestedAffineData
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m) (inverse forward : ℝ → ℝ)
    (graph : ℝ → X) (stable : ℝ × X → Y)
    (hinverse : ContDiff ℝ (m + 1) inverse)
    (hforward : ContDiff ℝ 1 forward) (hgraph : ContDiff ℝ m graph)
    (hstable : ContDiff ℝ (m + 1) stable) :
    ContDiff ℝ 1
        (sourceNestedPrincipalOperator m hm inverse forward graph stable) ∧
      ContDiff ℝ 1
        (sourceNestedEndpointForcing m inverse forward graph stable) := by
  constructor
  · exact (contDiffOne_nestedPrincipalOperator hm inverse graph stable
      hinverse hgraph hstable).comp hforward
  · exact (contDiffOne_nestedEndpointForcing hm inverse graph stable
      hinverse hgraph hstable).comp hforward

/-- Helper for Infrastructure I.16: an exact transported endpoint identity
turns the predecessor derivative value into its principal affine term plus the
factorial-normalized zero-top forcing. -/
private theorem iteratedDeriv_eq_nestedPrincipal_add_truncatedEndpoint
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} (hm : 0 < m) (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → X) (y : ℝ)
    (hendpoint :
      nestedEndpointJet m inverse graph stable y =
        FiniteTaylorJet.ofFunction ℝ m graph y) :
    iteratedDeriv m graph y =
      nestedPrincipalOperator m hm inverse graph stable y
        (iteratedDeriv m graph (inverse y)) +
      nestedEndpointForcing m inverse graph stable y := by
  have hsplit := nestedEndpointJet_topCoeff_sub_truncated_apply
    hm inverse graph stable y
  have hfactorial_ne : (m.factorial : ℝ) ≠ 0 := by
    positivity
  have htarget :
      ((nestedEndpointJet m inverse graph stable y).coeff
          ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ (1 : ℝ))) =
        ((m.factorial : ℝ)⁻¹) • iteratedDeriv m graph y := by
    rw [hendpoint, FiniteTaylorJet.coeff_ofFunction_apply]
    rfl
  have hsource :
      ((FiniteTaylorJet.ofFunction ℝ m graph (inverse y)).coeff
          ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ (1 : ℝ))) =
        ((m.factorial : ℝ)⁻¹) • iteratedDeriv m graph (inverse y) := by
    rw [FiniteTaylorJet.coeff_ofFunction_apply]
    rfl
  rw [sub_apply, htarget, hsource, map_smul] at hsplit
  have hscaled := congrArg (fun z : X ↦ (m.factorial : ℝ) • z) hsplit
  simp only [smul_sub, smul_smul,
    mul_inv_cancel₀ hfactorial_ne, one_smul] at hscaled
  simpa only [nestedEndpointForcing] using sub_eq_iff_eq_add.mp hscaled

/-- Helper for Infrastructure I.16: inverse cancellation transports the exact
output-coordinate predecessor value equation into source coordinates. -/
private theorem iteratedDeriv_sourceNestedAffineEquation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} (hm : 0 < m) (inverse forward : ℝ → ℝ)
    (graph : ℝ → X) (stable : ℝ × X → X)
    (hinverse_forward : ∀ x, inverse (forward x) = x)
    (hendpoint : ∀ y,
      nestedEndpointJet m inverse graph stable y =
        FiniteTaylorJet.ofFunction ℝ m graph y)
    (x : ℝ) :
    iteratedDeriv m graph (forward x) =
      sourceNestedPrincipalOperator m hm inverse forward graph stable x
        (iteratedDeriv m graph x) +
      sourceNestedEndpointForcing m inverse forward graph stable x := by
  have hvalue := iteratedDeriv_eq_nestedPrincipal_add_truncatedEndpoint
    hm inverse graph stable (forward x) (hendpoint (forward x))
  simpa only [sourceNestedPrincipalOperator, sourceNestedEndpointForcing,
    hinverse_forward] using hvalue

/-- Helper for Infrastructure I.16: a fixed graph equation identifies the
twice-composed output-coordinate endpoint jet with the graph jet itself. -/
private theorem nestedEndpointJet_eq_of_fixedEquation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} (inverse : ℝ → ℝ) (graph : ℝ → X)
    (stable : ℝ × X → X) (hinverse : ContDiff ℝ m inverse)
    (hgraph : ContDiff ℝ m graph) (hstable : ContDiff ℝ m stable)
    (hfixed : ∀ y, graph y = stable (inverse y, graph (inverse y)))
    (y : ℝ) :
    nestedEndpointJet m inverse graph stable y =
      FiniteTaylorJet.ofFunction ℝ m graph y := by
  let graphParam : ℝ → ℝ × X := fun x ↦ (x, graph x)
  have hgraphParam : ContDiff ℝ m graphParam := by
    exact contDiff_id.prodMk hgraph
  have hparamJet :
      FiniteTaylorJet.prod
          (FiniteTaylorJet.ofFunction ℝ m id (inverse y))
          (FiniteTaylorJet.ofFunction ℝ m graph (inverse y)) =
        FiniteTaylorJet.ofFunction ℝ m graphParam (inverse y) := by
    simpa only [graphParam, id_eq] using
      (FiniteTaylorJet.ofFunction_prodMk
        (m := m) (a := inverse y) contDiffAt_id
        hgraph.contDiffAt).symm
  have hstableComp :
      FiniteTaylorJet.comp
          (FiniteTaylorJet.ofFunction ℝ m stable
            (inverse y, graph (inverse y)))
          (FiniteTaylorJet.ofFunction ℝ m graphParam (inverse y)) =
        FiniteTaylorJet.ofFunction ℝ m (stable ∘ graphParam)
          (inverse y) := by
    exact FiniteTaylorJet.comp_ofFunction_scalar
      hgraphParam.contDiffAt hstable.contDiffAt
  have houterComp :
      FiniteTaylorJet.comp
          (FiniteTaylorJet.ofFunction ℝ m (stable ∘ graphParam)
            (inverse y))
          (FiniteTaylorJet.ofFunction ℝ m inverse y) =
        FiniteTaylorJet.ofFunction ℝ m
          ((stable ∘ graphParam) ∘ inverse) y := by
    exact FiniteTaylorJet.comp_ofFunction_scalar
      hinverse.contDiffAt (hstable.comp hgraphParam).contDiffAt
  have hfunction : ((stable ∘ graphParam) ∘ inverse) = graph := by
    funext x
    exact (hfixed x).symm
  rw [nestedEndpointJet, hparamJet, hstableComp, houterComp, hfunction]

/-- Helper for Infrastructure I.16: compact support is preserved by every
scalar iterated derivative. -/
private theorem iteratedDeriv_hasCompactSupport
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℝ → X} (hf : HasCompactSupport f) (m : ℕ) :
    HasCompactSupport (iteratedDeriv m f) := by
  induction m with
  | zero =>
      simpa only [iteratedDeriv_zero] using hf
  | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- Helper for Infrastructure I.16: a continuous compactly supported normed
space-valued function has a nonnegative uniform norm bound. -/
private theorem exists_nnreal_norm_bound_of_continuous_compactSupport
    {E X : Type*} [TopologicalSpace E] [NormedAddCommGroup X]
    (f : E → X) (hf : Continuous f) (hsupport : HasCompactSupport f) :
    ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ (C : ℝ) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hsupport
  let Cnonneg : ℝ := max C 0
  have hCnonneg : 0 ≤ Cnonneg := by
    dsimp only [Cnonneg]
    exact le_max_right _ _
  refine ⟨Real.toNNReal Cnonneg, ?_⟩
  intro x
  rw [Real.coe_toNNReal Cnonneg hCnonneg]
  exact (hC x).trans (le_max_left _ _)

/-- Helper for Infrastructure I.16: the value update in the output-coordinate
affine Picard operator. -/
private def affinePicardValue
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (inverse : ℝ → ℝ) (coefficient : ℝ → X →L[ℝ] X)
    (forcing : ℝ → X) (valueSection : BoundedContinuousFunction ℝ X)
    (y : ℝ) : X :=
  coefficient y (valueSection (inverse y)) + forcing y

/-- Helper for Infrastructure I.16: the weighted derivative update associated
to the output-coordinate affine Picard operator. -/
private noncomputable def weightedAffinePicardDerivativeValue
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : ℝ) (inverse : ℝ → ℝ)
    (coefficient : ℝ → X →L[ℝ] X) (forcing : ℝ → X)
    (valueSection weightedDerivative : BoundedContinuousFunction ℝ X)
    (y : ℝ) : X :=
  weight • deriv coefficient y (valueSection (inverse y)) +
    deriv inverse y • coefficient y (weightedDerivative (inverse y)) +
    weight • deriv forcing y

/-- Helper for Infrastructure I.16: rescaling the weighted derivative update
recovers the ordinary chain-rule derivative of the affine Picard value. -/
private theorem weightedAffinePicardDerivativeValue_rescale
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : ℝ) (hweight : weight ≠ 0) (inverse : ℝ → ℝ)
    (coefficient : ℝ → X →L[ℝ] X) (forcing : ℝ → X)
    (valueSection weightedDerivative : BoundedContinuousFunction ℝ X)
    (y : ℝ) :
    weight⁻¹ • weightedAffinePicardDerivativeValue weight inverse
        coefficient forcing valueSection weightedDerivative y =
      deriv coefficient y (valueSection (inverse y)) +
        coefficient y
          (deriv inverse y •
            (weight⁻¹ • weightedDerivative (inverse y))) +
        deriv forcing y := by
  simp only [weightedAffinePicardDerivativeValue, smul_add, smul_smul,
    inv_mul_cancel₀ hweight, one_smul, map_smul]
  rw [mul_comm weight⁻¹ (deriv inverse y)]

/-- Helper for Infrastructure I.16: two affine Picard value updates differ
only through their input sections. -/
private theorem affinePicardValue_sub
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (inverse : ℝ → ℝ) (coefficient : ℝ → X →L[ℝ] X)
    (forcing : ℝ → X) (section₁ section₂ : BoundedContinuousFunction ℝ X)
    (y : ℝ) :
    affinePicardValue inverse coefficient forcing section₁ y -
        affinePicardValue inverse coefficient forcing section₂ y =
      coefficient y
        (section₁ (inverse y) - section₂ (inverse y)) := by
  simp only [affinePicardValue, map_sub]
  abel

/-- Helper for Infrastructure I.16: the difference of two weighted derivative
updates contains one value error and one weighted-derivative error. -/
private theorem weightedAffinePicardDerivativeValue_sub
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : ℝ) (inverse : ℝ → ℝ)
    (coefficient : ℝ → X →L[ℝ] X) (forcing : ℝ → X)
    (section₁ section₂ weightedDerivative₁ weightedDerivative₂ :
      BoundedContinuousFunction ℝ X) (y : ℝ) :
    weightedAffinePicardDerivativeValue weight inverse coefficient forcing
        section₁ weightedDerivative₁ y -
      weightedAffinePicardDerivativeValue weight inverse coefficient forcing
        section₂ weightedDerivative₂ y =
      weight • deriv coefficient y
        (section₁ (inverse y) - section₂ (inverse y)) +
      deriv inverse y • coefficient y
        (weightedDerivative₁ (inverse y) -
          weightedDerivative₂ (inverse y)) := by
  simp only [weightedAffinePicardDerivativeValue, map_sub, smul_sub]
  abel

/-- Helper for Infrastructure I.16: a bounded solution of a fiberwise affine
fixed-point equation is `C¹` when the value and inverse-center derivative
contractions are both strict. -/
private theorem contDiffOne_of_affinePicard_fixedPoint
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X]
    (inverse : ℝ → ℝ) (coefficient : ℝ → X →L[ℝ] X)
    (forcing fixedSection : ℝ → X)
    (P C MA BF BDF BW : ℝ≥0)
    (hinverse : ContDiff ℝ 1 inverse)
    (hcoefficient : ContDiff ℝ 1 coefficient)
    (hforcing : ContDiff ℝ 1 forcing)
    (hfixedSection : Continuous fixedSection)
    (hfixed : ∀ y, fixedSection y =
      coefficient y (fixedSection (inverse y)) + forcing y)
    (hP_lt : P < 1) (hPC_lt : P * C < 1)
    (hcoefficient_norm : ∀ y, ‖coefficient y‖ ≤ (P : ℝ))
    (hinverse_deriv_norm : ∀ y, ‖deriv inverse y‖ ≤ (C : ℝ))
    (hcoefficient_deriv_norm : ∀ y, ‖deriv coefficient y‖ ≤ (MA : ℝ))
    (hforcing_norm : ∀ y, ‖forcing y‖ ≤ (BF : ℝ))
    (hforcing_deriv_norm : ∀ y, ‖deriv forcing y‖ ≤ (BDF : ℝ))
    (hfixedSection_norm : ∀ y, ‖fixedSection y‖ ≤ (BW : ℝ)) :
    ContDiff ℝ 1 fixedSection := by
  let q : ℝ := ((P * C : ℝ≥0) : ℝ)
  have hq_nonneg : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hP_nonneg : 0 ≤ (P : ℝ) := NNReal.coe_nonneg P
  have hMA_nonneg : 0 ≤ (MA : ℝ) := NNReal.coe_nonneg MA
  have hq_lt : q < 1 := by
    dsimp only [q]
    exact_mod_cast hPC_lt
  let weight : ℝ := (1 - q) / (2 * ((MA : ℝ) + 1))
  have hweight_pos : 0 < weight := by
    dsimp only [weight]
    positivity
  have hweight_ne : weight ≠ 0 := hweight_pos.ne'
  have hweight_mul_MA_le :
      weight * (MA : ℝ) ≤ (1 - q) / 2 := by
    calc
      weight * (MA : ℝ) ≤ weight * ((MA : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · exact hweight_pos.le
      _ = (1 - q) / 2 := by
        dsimp only [weight]
        field_simp
  let secondary : ℝ := q + weight * (MA : ℝ)
  have hsecondary_nonneg : 0 ≤ secondary := by
    dsimp only [secondary]
    positivity
  have hsecondary_lt : secondary < 1 := by
    dsimp only [secondary]
    nlinarith
  have hP_real_lt : (P : ℝ) < 1 := by
    exact_mod_cast hP_lt
  have hcontraction_nonneg :
      0 ≤ max (P : ℝ) secondary :=
    hP_nonneg.trans (le_max_left _ _)
  let K : ℝ≥0 := ⟨max (P : ℝ) secondary, hcontraction_nonneg⟩
  have hK_lt : K < 1 := by
    exact_mod_cast (max_lt hP_real_lt hsecondary_lt)
  have hvalue_continuous (valueSection : BoundedContinuousFunction ℝ X) :
      Continuous (affinePicardValue inverse coefficient forcing valueSection) := by
    unfold affinePicardValue
    exact (hcoefficient.continuous.clm_apply
      (valueSection.continuous.comp hinverse.continuous)).add hforcing.continuous
  have hvalue_norm_le (valueSection : BoundedContinuousFunction ℝ X) (y : ℝ) :
      ‖affinePicardValue inverse coefficient forcing valueSection y‖ ≤
        (P : ℝ) * ‖valueSection‖ + (BF : ℝ) := by
    calc
      ‖affinePicardValue inverse coefficient forcing valueSection y‖ ≤
          ‖coefficient y (valueSection (inverse y))‖ + ‖forcing y‖ := by
        exact norm_add_le _ _
      _ ≤ ‖coefficient y‖ * ‖valueSection (inverse y)‖ + ‖forcing y‖ := by
        exact add_le_add ((coefficient y).le_opNorm _) le_rfl
      _ ≤ (P : ℝ) * ‖valueSection‖ + (BF : ℝ) := by
        gcongr
        · exact hcoefficient_norm y
        · exact BoundedContinuousFunction.norm_coe_le_norm valueSection (inverse y)
        · exact hforcing_norm y
  let valueOperator : BoundedContinuousFunction ℝ X →
      BoundedContinuousFunction ℝ X := fun valueSection ↦
    BoundedContinuousFunction.ofNormedAddCommGroup
      (affinePicardValue inverse coefficient forcing valueSection)
      (hvalue_continuous valueSection)
      ((P : ℝ) * ‖valueSection‖ + (BF : ℝ))
      (hvalue_norm_le valueSection)
  have hvalueOperator_apply (valueSection : BoundedContinuousFunction ℝ X) (y : ℝ) :
      valueOperator valueSection y =
        affinePicardValue inverse coefficient forcing valueSection y :=
    rfl
  have hvalueOperator_dist_apply
      (section₁ section₂ : BoundedContinuousFunction ℝ X) (y : ℝ) :
      dist (valueOperator section₁ y) (valueOperator section₂ y) ≤
        (P : ℝ) * dist section₁ section₂ := by
    rw [hvalueOperator_apply, hvalueOperator_apply, dist_eq_norm,
      affinePicardValue_sub]
    calc
      ‖coefficient y
          (section₁ (inverse y) - section₂ (inverse y))‖ ≤
          ‖coefficient y‖ *
            ‖section₁ (inverse y) - section₂ (inverse y)‖ :=
        (coefficient y).le_opNorm _
      _ ≤ (P : ℝ) *
            ‖section₁ (inverse y) - section₂ (inverse y)‖ := by
        gcongr
        exact hcoefficient_norm y
      _ ≤ (P : ℝ) * dist section₁ section₂ := by
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left
          (BoundedContinuousFunction.dist_coe_le_dist
            (f := section₁) (g := section₂) (inverse y)) hP_nonneg
  have hvalueOperator_contracting : ContractingWith P valueOperator :=
    BoundedContinuousFunction.contractingWith_of_dist_apply_le_mul
      hP_lt hvalueOperator_dist_apply
  have hcoefficient_deriv_continuous : Continuous (deriv coefficient) :=
    hcoefficient.continuous_deriv le_rfl
  have hinverse_deriv_continuous : Continuous (deriv inverse) :=
    hinverse.continuous_deriv le_rfl
  have hforcing_deriv_continuous : Continuous (deriv forcing) :=
    hforcing.continuous_deriv le_rfl
  have hderivativeValue_continuous
      (valueSection weightedDerivative : BoundedContinuousFunction ℝ X) :
      Continuous (weightedAffinePicardDerivativeValue weight inverse
        coefficient forcing valueSection weightedDerivative) := by
    unfold weightedAffinePicardDerivativeValue
    have hfirst : Continuous (fun y ↦
        weight • deriv coefficient y (valueSection (inverse y))) :=
      continuous_const.smul
        (hcoefficient_deriv_continuous.clm_apply
          (valueSection.continuous.comp hinverse.continuous))
    have hsecond : Continuous (fun y ↦
        deriv inverse y •
          coefficient y (weightedDerivative (inverse y))) :=
      hinverse_deriv_continuous.smul
        (hcoefficient.continuous.clm_apply
          (weightedDerivative.continuous.comp hinverse.continuous))
    have hthird : Continuous (fun y ↦ weight • deriv forcing y) :=
      continuous_const.smul hforcing_deriv_continuous
    exact (hfirst.add hsecond).add hthird
  have hderivativeValue_norm_le
      (valueSection weightedDerivative : BoundedContinuousFunction ℝ X) (y : ℝ) :
      ‖weightedAffinePicardDerivativeValue weight inverse coefficient forcing
          valueSection weightedDerivative y‖ ≤
        weight * (MA : ℝ) * ‖valueSection‖ + q * ‖weightedDerivative‖ +
          weight * (BDF : ℝ) := by
    have hfirst :
        ‖weight • deriv coefficient y (valueSection (inverse y))‖ ≤
          weight * (MA : ℝ) * ‖valueSection‖ := by
      rw [norm_smul, Real.norm_of_nonneg hweight_pos.le]
      calc
        weight * ‖deriv coefficient y (valueSection (inverse y))‖ ≤
            weight * (‖deriv coefficient y‖ *
              ‖valueSection (inverse y)‖) := by
          gcongr
          exact (deriv coefficient y).le_opNorm _
        _ ≤ weight * ((MA : ℝ) * ‖valueSection‖) := by
          gcongr
          · exact hcoefficient_deriv_norm y
          · exact BoundedContinuousFunction.norm_coe_le_norm
              valueSection (inverse y)
        _ = weight * (MA : ℝ) * ‖valueSection‖ := by ring
    have hsecond :
        ‖deriv inverse y •
            coefficient y (weightedDerivative (inverse y))‖ ≤
          q * ‖weightedDerivative‖ := by
      rw [norm_smul]
      calc
        ‖deriv inverse y‖ *
            ‖coefficient y (weightedDerivative (inverse y))‖ ≤
            ‖deriv inverse y‖ *
              (‖coefficient y‖ *
                ‖weightedDerivative (inverse y)‖) := by
          gcongr
          exact (coefficient y).le_opNorm _
        _ ≤ (C : ℝ) * ((P : ℝ) * ‖weightedDerivative‖) := by
          gcongr
          · exact hinverse_deriv_norm y
          · exact hcoefficient_norm y
          · exact BoundedContinuousFunction.norm_coe_le_norm
              weightedDerivative (inverse y)
        _ = q * ‖weightedDerivative‖ := by
          dsimp only [q]
          simp only [NNReal.coe_mul]
          ring
    have hthird : ‖weight • deriv forcing y‖ ≤ weight * (BDF : ℝ) := by
      rw [norm_smul, Real.norm_of_nonneg hweight_pos.le]
      exact mul_le_mul_of_nonneg_left (hforcing_deriv_norm y) hweight_pos.le
    calc
      ‖weightedAffinePicardDerivativeValue weight inverse coefficient forcing
          valueSection weightedDerivative y‖ ≤
          ‖weight • deriv coefficient y (valueSection (inverse y))‖ +
            ‖deriv inverse y •
              coefficient y (weightedDerivative (inverse y))‖ +
            ‖weight • deriv forcing y‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ weight * (MA : ℝ) * ‖valueSection‖ +
          q * ‖weightedDerivative‖ + weight * (BDF : ℝ) :=
        add_le_add (add_le_add hfirst hsecond) hthird
  let derivativeOperator
      (valueSection weightedDerivative : BoundedContinuousFunction ℝ X) :
      BoundedContinuousFunction ℝ X :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (weightedAffinePicardDerivativeValue weight inverse coefficient forcing
        valueSection weightedDerivative)
      (hderivativeValue_continuous valueSection weightedDerivative)
      (weight * (MA : ℝ) * ‖valueSection‖ + q * ‖weightedDerivative‖ +
        weight * (BDF : ℝ))
      (hderivativeValue_norm_le valueSection weightedDerivative)
  have hderivativeOperator_apply
      (valueSection weightedDerivative : BoundedContinuousFunction ℝ X) (y : ℝ) :
      derivativeOperator valueSection weightedDerivative y =
        weightedAffinePicardDerivativeValue weight inverse coefficient forcing
          valueSection weightedDerivative y :=
    rfl
  have hderivativeOperator_dist
      (section₁ section₂ weightedDerivative₁ weightedDerivative₂ :
        BoundedContinuousFunction ℝ X) :
      dist (derivativeOperator section₁ weightedDerivative₁)
          (derivativeOperator section₂ weightedDerivative₂) ≤
        secondary * max (dist section₁ section₂)
          (dist weightedDerivative₁ weightedDerivative₂) := by
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro y
    rw [hderivativeOperator_apply, hderivativeOperator_apply, dist_eq_norm,
      weightedAffinePicardDerivativeValue_sub]
    have hvalue_eval :
        dist (section₁ (inverse y)) (section₂ (inverse y)) ≤
          dist section₁ section₂ :=
      BoundedContinuousFunction.dist_coe_le_dist
        (f := section₁) (g := section₂) (inverse y)
    have hderivative_eval :
        dist (weightedDerivative₁ (inverse y))
            (weightedDerivative₂ (inverse y)) ≤
          dist weightedDerivative₁ weightedDerivative₂ :=
      BoundedContinuousFunction.dist_coe_le_dist
        (f := weightedDerivative₁) (g := weightedDerivative₂) (inverse y)
    have hfirst :
        ‖weight • deriv coefficient y
            (section₁ (inverse y) - section₂ (inverse y))‖ ≤
          weight * (MA : ℝ) * dist section₁ section₂ := by
      rw [norm_smul, Real.norm_of_nonneg hweight_pos.le]
      calc
        weight * ‖deriv coefficient y
            (section₁ (inverse y) - section₂ (inverse y))‖ ≤
            weight * (‖deriv coefficient y‖ *
              ‖section₁ (inverse y) - section₂ (inverse y)‖) := by
          gcongr
          exact (deriv coefficient y).le_opNorm _
        _ ≤ weight * ((MA : ℝ) * dist section₁ section₂) := by
          gcongr
          · exact hcoefficient_deriv_norm y
          · simpa only [dist_eq_norm] using hvalue_eval
        _ = weight * (MA : ℝ) * dist section₁ section₂ := by ring
    have hsecond :
        ‖deriv inverse y • coefficient y
            (weightedDerivative₁ (inverse y) -
              weightedDerivative₂ (inverse y))‖ ≤
          q * dist weightedDerivative₁ weightedDerivative₂ := by
      rw [norm_smul]
      calc
        ‖deriv inverse y‖ *
            ‖coefficient y
              (weightedDerivative₁ (inverse y) -
                weightedDerivative₂ (inverse y))‖ ≤
            ‖deriv inverse y‖ *
              (‖coefficient y‖ *
                ‖weightedDerivative₁ (inverse y) -
                  weightedDerivative₂ (inverse y)‖) := by
          gcongr
          exact (coefficient y).le_opNorm _
        _ ≤ (C : ℝ) * ((P : ℝ) *
              dist weightedDerivative₁ weightedDerivative₂) := by
          gcongr
          · exact hinverse_deriv_norm y
          · exact hcoefficient_norm y
          · simpa only [dist_eq_norm] using hderivative_eval
        _ = q * dist weightedDerivative₁ weightedDerivative₂ := by
          dsimp only [q]
          simp only [NNReal.coe_mul]
          ring
    calc
      ‖weight • deriv coefficient y
          (section₁ (inverse y) - section₂ (inverse y)) +
        deriv inverse y • coefficient y
          (weightedDerivative₁ (inverse y) -
            weightedDerivative₂ (inverse y))‖ ≤
          ‖weight • deriv coefficient y
            (section₁ (inverse y) - section₂ (inverse y))‖ +
          ‖deriv inverse y • coefficient y
            (weightedDerivative₁ (inverse y) -
              weightedDerivative₂ (inverse y))‖ := norm_add_le _ _
      _ ≤ weight * (MA : ℝ) * dist section₁ section₂ +
          q * dist weightedDerivative₁ weightedDerivative₂ :=
        add_le_add hfirst hsecond
      _ ≤ weight * (MA : ℝ) *
            max (dist section₁ section₂)
              (dist weightedDerivative₁ weightedDerivative₂) +
          q * max (dist section₁ section₂)
              (dist weightedDerivative₁ weightedDerivative₂) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _)
            (mul_nonneg hweight_pos.le hMA_nonneg)
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hq_nonneg
      _ = secondary * max (dist section₁ section₂)
          (dist weightedDerivative₁ weightedDerivative₂) := by
        dsimp only [secondary]
        ring
  let jointOperator :
      (BoundedContinuousFunction ℝ X × BoundedContinuousFunction ℝ X) →
        (BoundedContinuousFunction ℝ X × BoundedContinuousFunction ℝ X) :=
    fun state ↦
      (valueOperator state.1, derivativeOperator state.1 state.2)
  have hK_coe : (K : ℝ) = max (P : ℝ) secondary := rfl
  have hjointOperator_contracting : ContractingWith K jointOperator := by
    refine ⟨hK_lt, LipschitzWith.of_dist_le_mul ?_⟩
    intro state₁ state₂
    rw [Prod.dist_eq, Prod.dist_eq]
    apply max_le
    · calc
        dist (jointOperator state₁).1 (jointOperator state₂).1 =
            dist (valueOperator state₁.1) (valueOperator state₂.1) := rfl
        _ ≤ (P : ℝ) * dist state₁.1 state₂.1 := by
          apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
          exact hvalueOperator_dist_apply state₁.1 state₂.1
        _ ≤ (K : ℝ) * max (dist state₁.1 state₂.1)
            (dist state₁.2 state₂.2) := by
          apply mul_le_mul
          · rw [hK_coe]
            exact le_max_left _ _
          · exact le_max_left _ _
          · exact dist_nonneg
          · positivity
    · calc
        dist (jointOperator state₁).2 (jointOperator state₂).2 =
            dist (derivativeOperator state₁.1 state₁.2)
              (derivativeOperator state₂.1 state₂.2) := rfl
        _ ≤ secondary * max (dist state₁.1 state₂.1)
            (dist state₁.2 state₂.2) :=
          hderivativeOperator_dist state₁.1 state₂.1 state₁.2 state₂.2
        _ ≤ (K : ℝ) * max (dist state₁.1 state₂.1)
            (dist state₁.2 state₂.2) := by
          apply mul_le_mul_of_nonneg_right
          · rw [hK_coe]
            exact le_max_right _ _
          · exact dist_nonneg.trans (le_max_left _ _)
  let fixedBoundedSection : BoundedContinuousFunction ℝ X :=
    BoundedContinuousFunction.ofNormedAddCommGroup fixedSection
      hfixedSection (BW : ℝ) hfixedSection_norm
  have hfixedBoundedSection_isFixed :
      Function.IsFixedPt valueOperator fixedBoundedSection := by
    ext y
    exact (hfixed y).symm
  let initialState :
      BoundedContinuousFunction ℝ X × BoundedContinuousFunction ℝ X := (0, 0)
  let stateSequence : ℕ →
      BoundedContinuousFunction ℝ X × BoundedContinuousFunction ℝ X :=
    fun n ↦ jointOperator^[n] initialState
  let fixedState := ContractingWith.fixedPoint jointOperator
    hjointOperator_contracting
  have hstateSequence_tendsto :
      Tendsto stateSequence atTop (𝓝 fixedState) := by
    simpa only [stateSequence] using
      hjointOperator_contracting.tendsto_iterate_fixedPoint initialState
  have hfixedState_isFixed : Function.IsFixedPt jointOperator fixedState :=
    hjointOperator_contracting.fixedPoint_isFixedPt
  have hfixedState_first_isFixed :
      Function.IsFixedPt valueOperator fixedState.1 := by
    have hfirst := congrArg Prod.fst hfixedState_isFixed
    change valueOperator fixedState.1 = fixedState.1
    simpa only [jointOperator] using hfirst
  have hfixedState_first_eq : fixedState.1 = fixedBoundedSection :=
    hvalueOperator_contracting.fixedPoint_unique'
      hfixedState_first_isFixed hfixedBoundedSection_isFixed
  let functionSequence : ℕ → BoundedContinuousFunction ℝ X :=
    fun n ↦ (stateSequence n).1
  let weightedDerivativeSequence : ℕ → BoundedContinuousFunction ℝ X :=
    fun n ↦ (stateSequence n).2
  let derivativeSequence : ℕ → BoundedContinuousFunction ℝ X :=
    fun n ↦ weight⁻¹ • weightedDerivativeSequence n
  let derivativeLimit : BoundedContinuousFunction ℝ X :=
    weight⁻¹ • fixedState.2
  have hfunctionSequence_tendsto :
      Tendsto functionSequence atTop (𝓝 fixedBoundedSection) := by
    have hfirst : Tendsto (fun n ↦ (stateSequence n).1) atTop
        (𝓝 fixedState.1) :=
      continuous_fst.continuousAt.tendsto.comp hstateSequence_tendsto
    simpa only [functionSequence, hfixedState_first_eq] using hfirst
  have hweightedDerivativeSequence_tendsto :
      Tendsto weightedDerivativeSequence atTop (𝓝 fixedState.2) := by
    exact continuous_snd.continuousAt.tendsto.comp hstateSequence_tendsto
  have hderivativeSequence_tendsto :
      Tendsto derivativeSequence atTop (𝓝 derivativeLimit) := by
    simpa only [derivativeSequence, derivativeLimit] using
      hweightedDerivativeSequence_tendsto.const_smul weight⁻¹
  have hstateSequence_succ (n : ℕ) :
      stateSequence (n + 1) = jointOperator (stateSequence n) := by
    simp only [stateSequence, Function.iterate_succ_apply']
  have hfunctionSequence_zero : functionSequence 0 = 0 := by
    rfl
  have hweightedDerivativeSequence_zero :
      weightedDerivativeSequence 0 = 0 := by
    rfl
  have hfunctionSequence_succ (n : ℕ) :
      functionSequence (n + 1) = valueOperator (functionSequence n) := by
    have hstate := congrArg Prod.fst (hstateSequence_succ n)
    simpa only [functionSequence, jointOperator] using hstate
  have hweightedDerivativeSequence_succ (n : ℕ) :
      weightedDerivativeSequence (n + 1) =
        derivativeOperator (functionSequence n)
          (weightedDerivativeSequence n) := by
    have hstate := congrArg Prod.snd (hstateSequence_succ n)
    simpa only [functionSequence, weightedDerivativeSequence,
      jointOperator] using hstate
  have hderivativeSequence_succ_apply (n : ℕ) (y : ℝ) :
      derivativeSequence (n + 1) y =
        weight⁻¹ • weightedAffinePicardDerivativeValue weight inverse
          coefficient forcing (functionSequence n)
          (weightedDerivativeSequence n) y := by
    simp only [derivativeSequence, BoundedContinuousFunction.coe_smul,
      hweightedDerivativeSequence_succ, hderivativeOperator_apply]
  have hfunctionSequence_hasDeriv :
      ∀ n y, HasDerivAt (functionSequence n)
        (derivativeSequence n y) y := by
    intro n
    induction n with
    | zero =>
        intro y
        rw [hfunctionSequence_zero]
        have hderivative_zero : derivativeSequence 0 y = 0 := by
          simp only [derivativeSequence, hweightedDerivativeSequence_zero,
            smul_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply]
        rw [hderivative_zero]
        change HasDerivAt (fun _ : ℝ ↦ (0 : X)) 0 y
        exact hasDerivAt_const y 0
    | succ n ih =>
        intro y
        rw [hfunctionSequence_succ]
        have hinverse_hasDeriv : HasDerivAt inverse (deriv inverse y) y :=
          (hinverse.differentiable one_ne_zero y).hasDerivAt
        have hcomposite : HasDerivAt
            (functionSequence n ∘ inverse)
            (deriv inverse y • derivativeSequence n (inverse y)) y :=
          (ih (inverse y)).scomp y hinverse_hasDeriv
        have hcoefficient_hasDeriv :
            HasDerivAt coefficient (deriv coefficient y) y :=
          (hcoefficient.differentiable one_ne_zero y).hasDerivAt
        have hforcing_hasDeriv : HasDerivAt forcing (deriv forcing y) y :=
          (hforcing.differentiable one_ne_zero y).hasDerivAt
        have hupdate := hcoefficient_hasDeriv.clm_apply hcomposite
        have hupdate_forcing := hupdate.add hforcing_hasDeriv
        have hvalueOperator_eq :
            (valueOperator (functionSequence n) : ℝ → X) =
              affinePicardValue inverse coefficient forcing
                (functionSequence n) := by
          funext z
          exact hvalueOperator_apply (functionSequence n) z
        rw [hvalueOperator_eq]
        have haffinePicardValue_eq :
            affinePicardValue inverse coefficient forcing
                (functionSequence n) =
              (fun z ↦ coefficient z
                (functionSequence n (inverse z))) + forcing := by
          funext z
          rfl
        rw [haffinePicardValue_eq]
        have hscaled := weightedAffinePicardDerivativeValue_rescale
          weight hweight_ne inverse coefficient forcing
          (functionSequence n) (weightedDerivativeSequence n) y
        rw [hderivativeSequence_succ_apply, hscaled]
        simpa only [Function.comp_def, derivativeSequence,
          BoundedContinuousFunction.coe_smul,
          smul_smul] using hupdate_forcing
  have hvalue_tendsto (y : ℝ) :
      Tendsto (fun n ↦ functionSequence n y) atTop
        (𝓝 (fixedSection y)) := by
    have heval :=
      ((BoundedContinuousFunction.lipschitz_eval_const y).continuous.continuousAt.tendsto).comp
        hfunctionSequence_tendsto
    simpa only [Function.comp_def, fixedBoundedSection,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup] using heval
  have hderivativeSequence_uniform :
      TendstoUniformly (fun n ↦ derivativeSequence n) derivativeLimit atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      hderivativeSequence_tendsto
  have hfixedSection_hasDeriv (y : ℝ) :
      HasDerivAt fixedSection (derivativeLimit y) y :=
    hasDerivAt_of_tendstoUniformly hderivativeSequence_uniform
      (Filter.Eventually.of_forall hfunctionSequence_hasDeriv)
      hvalue_tendsto y
  rw [contDiff_one_iff_deriv]
  constructor
  · intro y
    exact (hfixedSection_hasDeriv y).differentiableAt
  · have hderiv_eq : deriv fixedSection = derivativeLimit := by
      funext y
      exact (hfixedSection_hasDeriv y).deriv
    rw [hderiv_eq]
    exact derivativeLimit.continuous

/-- Helper for Infrastructure I.16: stable output coefficients below the top
order are invariant under a top input update. -/
private theorem stableJet_coeff_eq_of_topUpdate_below
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {radius slope : ℝ≥0}
    (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J : BoundedGraphJet X radius slope r)
    (hr : 0 < r) (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (u : ℝ) (k : Fin (r + 1)) (hk : (k : ℕ) < r) :
    (JetTransform.stableJet r χ ρ L N
      (JetTransform.topUpdatedGraphJet r hr J a) u).coeff k =
      (JetTransform.stableJet r χ ρ L N J u).coeff k := by
  -- The graph-parametrization coefficients agree through the target order.
  have hparamCoeff (j : Fin (r + 1)) (hj : (j : ℕ) ≤ (k : ℕ)) :
      (JetTransform.graphParametrizationJet r
        (JetTransform.topUpdatedGraphJet r hr J a) u).coeff j =
        (JetTransform.graphParametrizationJet r J u).coeff j := by
    rw [JetTransform.graphParametrizationJet, JetTransform.graphParametrizationJet,
      FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod]
    rw [JetTransform.topUpdatedGraphJet_coeff_of_lt r hr J a u j
      (lt_of_le_of_lt hj hk)]
  have hparamConstant :
      (JetTransform.graphParametrizationJet r
        (JetTransform.topUpdatedGraphJet r hr J a) u).constantCoeff =
        (JetTransform.graphParametrizationJet r J u).constantCoeff := by
    have hcoeff := hparamCoeff (0 : Fin (r + 1)) (Nat.zero_le _)
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (JetTransform.graphParametrizationJet r
        (JetTransform.topUpdatedGraphJet r hr J a) u).constantCoeff =
          (JetTransform.graphParametrizationJet r
            (JetTransform.topUpdatedGraphJet r hr J a) u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (JetTransform.graphParametrizationJet r J u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) := hcoeffValue
      _ = (JetTransform.graphParametrizationJet r J u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  -- The postcomposition with the cutoff map preserves these lower coefficients.
  have himageCoeff (j : Fin (r + 1)) (hj : (j : ℕ) ≤ (k : ℕ)) :
      (JetTransform.imageJet r χ ρ L N
        (JetTransform.topUpdatedGraphJet r hr J a) u).coeff j =
        (JetTransform.imageJet r χ ρ L N J u).coeff j := by
    rw [JetTransform.imageJet, JetTransform.imageJet, FiniteTaylorJet.postcomp_def,
      FiniteTaylorJet.postcomp_def, hparamConstant]
    apply JetTransform.finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro i _
      rfl
    · intro i hi_pos hi_le
      exact hparamCoeff i (hi_le.trans hj)
  have himageConstant :
      (JetTransform.imageJet r χ ρ L N
        (JetTransform.topUpdatedGraphJet r hr J a) u).constantCoeff =
        (JetTransform.imageJet r χ ρ L N J u).constantCoeff := by
    have hcoeff := himageCoeff (0 : Fin (r + 1)) (Nat.zero_le _)
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (JetTransform.imageJet r χ ρ L N
        (JetTransform.topUpdatedGraphJet r hr J a) u).constantCoeff =
          (JetTransform.imageJet r χ ρ L N
            (JetTransform.topUpdatedGraphJet r hr J a) u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (JetTransform.imageJet r χ ρ L N J u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) := hcoeffValue
      _ = (JetTransform.imageJet r χ ρ L N J u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  rw [JetTransform.stableJet, JetTransform.stableJet,
    FiniteTaylorJet.postcomp_def,
    FiniteTaylorJet.postcomp_def, himageConstant]
  apply JetTransform.finiteTaylorJet_comp_coeff_eq_of_eq_below
  · intro j _
    rfl
  · intro j hj_pos hj_le
    exact himageCoeff j hj_le

/-- Helper for Infrastructure I.16: the top coefficient of a composition with
a top-truncated outer jet is the sum of its non-all-ones branches. -/
private theorem finiteTaylorJet_comp_topCoeff_nonOnes_eq_truncatedOuter
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (Q : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m) :
    (FiniteTaylorJet.comp (truncateTopCoeff Q) P).coeff
        ⟨m, Nat.lt_succ_self m⟩ =
      ∑ c : Composition m, if c = Composition.ones m then 0 else
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c := by
  simpa only [truncateTopCoeff] using
    FiniteTaylorJet.comp_topCoeff_nonOnes_eq_zeroTopReplacement Q P

/-- Helper for Infrastructure I.16: the differentiated top coefficient of a
top-updated graph jet is the all-ones branch plus the filtered non-ones sum. -/
private theorem differentiatedJet_topCoeff_branch_split
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {radius slope : ℝ≥0} (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (J : BoundedGraphJet X radius slope r)
    (hr : 0 < r) (b : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (v : ℝ) :
    (JetTransform.differentiatedJet r χ ρ L N (JetTransform.topUpdatedGraphJet r hr J b) v).coeff
        ⟨r, Nat.lt_succ_self r⟩ =
      ((JetTransform.stableJet r χ ρ L N (JetTransform.topUpdatedGraphJet r hr J b)
          (LocalCutoff.CenterProjection.inverse χ ρ L N
            (JetTransform.topUpdatedGraphJet r hr J b).graph v)).toFormalMultilinearSeries).compAlongComposition
          ((FiniteTaylorJet.ofFunction ℝ r
            (LocalCutoff.CenterProjection.inverse χ ρ L N
              (JetTransform.topUpdatedGraphJet r hr J b).graph) v).toFormalMultilinearSeries)
          (Composition.ones r) +
        ∑ c : Composition r, if c = Composition.ones r then 0 else
          ((JetTransform.stableJet r χ ρ L N (JetTransform.topUpdatedGraphJet r hr J b)
              (LocalCutoff.CenterProjection.inverse χ ρ L N
                (JetTransform.topUpdatedGraphJet r hr J b).graph v)).toFormalMultilinearSeries).compAlongComposition
            ((FiniteTaylorJet.ofFunction ℝ r
              (LocalCutoff.CenterProjection.inverse χ ρ L N
                (JetTransform.topUpdatedGraphJet r hr J b).graph) v).toFormalMultilinearSeries) c := by
  -- Expose only the coefficient-level composition formula; the graph update
  -- remains opaque and is used solely through its inherited graph field.
  simpa only [JetTransform.differentiatedJet] using
    (JetTransform.finiteTaylorJet_comp_topCoeff_branch_split
      (JetTransform.stableJet r χ ρ L N
        (JetTransform.topUpdatedGraphJet r hr J b)
        (LocalCutoff.CenterProjection.inverse χ ρ L N
          (JetTransform.topUpdatedGraphJet r hr J b).graph v))
      (FiniteTaylorJet.ofFunction ℝ r
        (LocalCutoff.CenterProjection.inverse χ ρ L N
          (JetTransform.topUpdatedGraphJet r hr J b).graph) v))

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): a finite
orbit iteration for an eventual affine recurrence on positive radii.
The explicit orbit hypothesis keeps the statement valid whether the scale `c`
shrinks or expands the radius. -/
private theorem scaledRecurrence_iterate_of_eventually
    {F g : ℝ → ℝ} {q c δ η : ℝ}
    (hq : 0 ≤ q) (hc : 0 < c)
    (hrec : ∀ x, 0 < x → x < δ → F x ≤ q * F (c * x) + g x)
    (hη : 0 < η) (n : ℕ)
    (horbit : ∀ j < n, 0 < c ^ j * η ∧ c ^ j * η < δ) :
    F η ≤ q ^ n * F (c ^ n * η) +
      Finset.sum (Finset.range n) (fun j ↦ q ^ j * g (c ^ j * η)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have horbit_prev : ∀ j < n, 0 < c ^ j * η ∧ c ^ j * η < δ := by
        intro j hj
        exact horbit j (hj.trans (Nat.lt_succ_self n))
      have hprev := ih horbit_prev
      have hstep_pos : 0 < c ^ n * η := by
        exact mul_pos (pow_pos hc n) hη
      have hstep_lt : c ^ n * η < δ := (horbit n (Nat.lt_succ_self n)).2
      have hstep := hrec (c ^ n * η) hstep_pos hstep_lt
      have hscaled := mul_le_mul_of_nonneg_left hstep (pow_nonneg hq n)
      calc
        F η ≤ q ^ n * F (c ^ n * η) +
            Finset.sum (Finset.range n) (fun j ↦ q ^ j * g (c ^ j * η)) := hprev
        _ ≤ q ^ n * (q * F (c * (c ^ n * η)) + g (c ^ n * η)) +
            Finset.sum (Finset.range n) (fun j ↦ q ^ j * g (c ^ j * η)) :=
          add_le_add_left hscaled _
        _ = q ^ (n + 1) * F (c ^ (n + 1) * η) +
            Finset.sum (Finset.range (n + 1)) (fun j ↦ q ^ j * g (c ^ j * η)) := by
          rw [Finset.sum_range_succ, pow_succ]
          ring_nf

/-- A finite weighted orbit estimate for the transported increment recurrence in
Infrastructure I.16. -/
private theorem weightedRecurrence_iterate
    {α : Type*} {F E : α → ℝ} {p : ℝ} (hp : 0 ≤ p) (n : ℕ) (t : α)
    (step : α → α) (hstep : ∀ s, F s ≤ p * F (step s) + E s) :
    F t ≤ p ^ n * F (step^[n] t) +
      ∑ j ∈ Finset.range n, p ^ j * E (step^[j] t) := by
  -- Iterate one transported increment at a time and expose the finite error sum.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        F t ≤ p ^ n * F (step^[n] t) +
            ∑ j ∈ Finset.range n, p ^ j * E (step^[j] t) := ih
        _ ≤ p ^ n * (p * F (step (step^[n] t)) + E (step^[n] t)) +
            ∑ j ∈ Finset.range n, p ^ j * E (step^[j] t) := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left (hstep _) (pow_nonneg hp _)) _
        _ = p ^ (n + 1) * F (step^[n + 1] t) +
            ∑ j ∈ Finset.range (n + 1), p ^ j * E (step^[j] t) := by
          rw [Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ]
          ring_nf

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): a
    bounded scalar recurrence with a uniform forcing term has the corresponding
    supremum bound. -/
private theorem norm_le_of_bounded_recurrence
    {α : Type*} [Nonempty α] {F E : α → ℝ} {step : α → α} {p e : ℝ}
    (hp : 0 ≤ p) (hp_lt : p < 1)
    (hbounded : BddAbove (Set.range F))
    (hnonempty : (Set.range F).Nonempty)
    (hstep : ∀ s, F s ≤ p * F (step s) + E s)
    (hE : ∀ s, E s ≤ e) :
    ∀ s, F s ≤ e / (1 - p) := by
  -- First replace each successor value by the global supremum of the orbit.
  have hsuccessor (s : α) : F (step s) ≤ sSup (Set.range F) := by
    exact le_csSup hbounded ⟨step s, rfl⟩
  have hpointwise (s : α) :
      F s ≤ p * sSup (Set.range F) + e := by
    calc
      F s ≤ p * F (step s) + E s := hstep s
      _ ≤ p * sSup (Set.range F) + E s := by
        linarith [mul_le_mul_of_nonneg_left (hsuccessor s) hp]
      _ ≤ p * sSup (Set.range F) + e := by
        linarith [hE s]
  have hsup : sSup (Set.range F) ≤
      p * sSup (Set.range F) + e := by
    apply csSup_le hnonempty
    rintro _ ⟨s, rfl⟩
    exact hpointwise s
  have hgap : 0 < 1 - p := sub_pos.mpr hp_lt
  have hsup_bound : sSup (Set.range F) ≤ e / (1 - p) := by
    apply (le_div_iff₀ hgap).mpr
    nlinarith
  intro s
  exact (le_csSup hbounded ⟨s, rfl⟩).trans hsup_bound

/-- A finite orbit of a weighted affine radius recurrence has a geometric
forcing budget whose ratio is the product of the recurrence and transport
factors. -/
private theorem weighted_radius_recurrence_iterate
    {F : ℝ → ℝ} {p c e δ x : ℝ}
    (hp : 0 ≤ p) (hc : 0 < c)
    (hrec : ∀ y, 0 < y → y < δ → F y ≤ p * F (c * y) + e * y)
    (hx : 0 < x) (n : ℕ)
    (horbit : ∀ j < n, 0 < c ^ j * x ∧ c ^ j * x < δ) :
    F x ≤ p ^ n * F (c ^ n * x) +
      e * x * ∑ j ∈ Finset.range n, (p * c) ^ j := by
  -- First iterate the recurrence without normalizing the forcing sum.
  have hiter := scaledRecurrence_iterate_of_eventually
    (F := F) (g := fun y ↦ e * y) (q := p) (c := c) (δ := δ)
    (η := x) hp hc hrec (by simpa using hx) n horbit
  calc
    F x ≤ p ^ n * F (c ^ n * x) +
        Finset.sum (Finset.range n) (fun j ↦ p ^ j * (e * (c ^ j * x))) := hiter
    _ = p ^ n * F (c ^ n * x) +
        e * x * ∑ j ∈ Finset.range n, (p * c) ^ j := by
      congr 1
      calc
        Finset.sum (Finset.range n) (fun j ↦ p ^ j * (e * (c ^ j * x))) =
            ∑ j ∈ Finset.range n, e * x * (p * c) ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_pow]
          ring
        _ = e * x * ∑ j ∈ Finset.range n, (p * c) ^ j := by
          rw [Finset.mul_sum]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): an
expanding geometric orbit starting below `δ / c` has a first point in the
annulus from `δ / c` to `δ`. -/
private theorem geometricOrbit_reaches_annulus
    {c δ x : ℝ} (hc : 1 < c) (hδ : 0 < δ) (hx : 0 < x)
    (hsmall : x < δ / c) :
    ∃ n : ℕ, δ / c ≤ c ^ n * x ∧ c ^ n * x < δ := by
  have htarget_pos : 0 < (δ / c) / x :=
    div_pos (div_pos hδ (zero_lt_one.trans hc)) hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((δ / c) / x) hc
  have hexists : ∃ n : ℕ, δ / c ≤ c ^ n * x := by
    refine ⟨n, ?_⟩
    have hmul := mul_lt_mul_of_pos_right hn hx
    calc
      δ / c = ((δ / c) / x) * x := by field_simp
      _ ≤ c ^ n * x := hmul.le
  let n₀ := Nat.find hexists
  have hn₀_lower : δ / c ≤ c ^ n₀ * x := Nat.find_spec hexists
  have hn₀_ne : n₀ ≠ 0 := by
    intro hzero
    have hlower := hn₀_lower
    rw [hzero, pow_zero, one_mul] at hlower
    exact (not_le_of_gt hsmall) hlower
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn₀_ne
  have hk_min : ¬δ / c ≤ c ^ k * x := by
    intro hk_lower
    have hn₀_le := Nat.find_min' hexists hk_lower
    change n₀ ≤ k at hn₀_le
    rw [hk] at hn₀_le
    exact (Nat.not_succ_le_self k) hn₀_le
  have hk_lt : c ^ k * x < δ / c := lt_of_not_ge hk_min
  refine ⟨n₀, hn₀_lower, ?_⟩
  rw [hk, pow_succ]
  calc
    c ^ k * c * x = c * (c ^ k * x) := by ring
    _ < c * (δ / c) :=
      mul_lt_mul_of_pos_left hk_lt (zero_lt_one.trans hc)
    _ = δ := by field_simp

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): a
monotone radius envelope with a locally bounded affine recurrence is sublinear
at zero when the recurrence factor times the transport factor is below one. -/
private theorem radiusEnvelope_sublinear_of_localRecurrence
    (F : ℝ → ℝ) (p c : ℝ)
    (hmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hp : 0 ≤ p) (hp_lt : p < 1) (hc : 0 < c) (hpc : p * c < 1)
    (hbounded : ∃ δ > 0, ∃ M ≥ 0, ∀ x, 0 ≤ x → x < δ → F x ≤ M)
    (hrec : ∀ e > 0, ∃ δ > 0, ∀ x, 0 < x → x < δ →
      F x ≤ p * F (c * x) + e * x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x → x < δ → F x ≤ ε * x := by
  intro ε hε
  by_cases hc_one : c ≤ 1
  · -- A nonexpanding transported radius is absorbed by monotonicity.
    have he_pos : 0 < ε * (1 - p) := mul_pos hε (sub_pos.mpr hp_lt)
    obtain ⟨δ, hδ, hδrec⟩ := hrec (ε * (1 - p)) he_pos
    refine ⟨δ, hδ, ?_⟩
    intro x hx hxδ
    have hcx_nonneg : 0 ≤ c * x := mul_nonneg hc.le hx.le
    have hcx_le : c * x ≤ x := by nlinarith
    have hFx := (hδrec x hx hxδ).trans <|
      add_le_add (mul_le_mul_of_nonneg_left
        (hmono hcx_nonneg hcx_le) hp) le_rfl
    nlinarith
  · -- For an expanding radius, stop at the first point in a fixed annulus.
    have hc_one_lt : 1 < c := lt_of_not_ge hc_one
    have hq_nonneg : 0 ≤ p * c := mul_nonneg hp hc.le
    obtain ⟨δb, hδb, M, hM, hMbound⟩ := hbounded
    have he_pos : 0 < ε * (1 - p * c) / 2 := by positivity
    obtain ⟨δr, hδr, hδrec⟩ := hrec (ε * (1 - p * c) / 2) he_pos
    let δ₀ := min δb δr
    have hδ₀ : 0 < δ₀ := lt_min hδb hδr
    let A := M * c / δ₀
    have hA : 0 ≤ A := div_nonneg (mul_nonneg hM hc.le) hδ₀.le
    have htarget : 0 < (ε / 2) / (A + 1) :=
      div_pos (half_pos hε) (by linarith)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one htarget hpc
    let δ := min (δ₀ / c) (δ₀ / c ^ (N + 1))
    have hδ : 0 < δ := lt_min (div_pos hδ₀ hc)
      (div_pos hδ₀ (pow_pos hc _))
    refine ⟨δ, hδ, ?_⟩
    intro x hx hxδ
    have hx_annulus : x < δ₀ / c := hxδ.trans_le (min_le_left _ _)
    obtain ⟨n, hn_lower, hn_upper⟩ :=
      geometricOrbit_reaches_annulus hc_one_lt hδ₀ hx hx_annulus
    have hNn : N ≤ n := by
      by_contra hnot
      have hnN : n < N := Nat.lt_of_not_ge hnot
      have hpow_le : c ^ n ≤ c ^ N := pow_le_pow_right₀ hc_one_lt.le hnN.le
      have hx_small : x < δ₀ / c ^ (N + 1) :=
        hxδ.trans_le (min_le_right _ _)
      have hmul := mul_lt_mul_of_pos_left hx_small (pow_pos hc n)
      have hterminal_lt : c ^ n * x < δ₀ / c := by
        calc
          c ^ n * x < c ^ n * (δ₀ / c ^ (N + 1)) := hmul
          _ ≤ c ^ N * (δ₀ / c ^ (N + 1)) := by
            exact mul_le_mul_of_nonneg_right hpow_le
              (div_nonneg hδ₀.le (pow_nonneg hc.le _))
          _ = δ₀ / c := by
            rw [pow_succ]
            field_simp
      exact (not_lt_of_ge hn_lower) hterminal_lt
    let G : ℝ → ℝ := fun y ↦ F y / y
    have hGrec : ∀ y, 0 < y → y < δ₀ →
        G y ≤ (p * c) * G (c * y) + ε * (1 - p * c) / 2 := by
      intro y hy hyδ₀
      have hyδr : y < δr := hyδ₀.trans_le (min_le_right _ _)
      have hraw := hδrec y hy hyδr
      have hcy : 0 < c * y := mul_pos hc hy
      dsimp only [G]
      calc
        F y / y ≤
            (p * F (c * y) + ε * (1 - p * c) / 2 * y) / y :=
          div_le_div_of_nonneg_right hraw hy.le
        _ = (p * c) * (F (c * y) / (c * y)) +
            ε * (1 - p * c) / 2 := by field_simp
    have horbit : ∀ j < n, 0 < c ^ j * x ∧ c ^ j * x < δ₀ := by
      intro j hj
      have hjn : c ^ j ≤ c ^ n := pow_le_pow_right₀ hc_one_lt.le hj.le
      refine ⟨mul_pos (pow_pos hc j) hx, ?_⟩
      exact (mul_le_mul_of_nonneg_right hjn hx.le).trans_lt hn_upper
    have hiter := scaledRecurrence_iterate_of_eventually
      (F := G) (g := fun _ ↦ ε * (1 - p * c) / 2)
      (q := p * c) (c := c) (δ := δ₀) (η := x)
      hq_nonneg hc hGrec hx n horbit
    have hiter' : G x ≤ (p * c) ^ n * G (c ^ n * x) +
        (ε * (1 - p * c) / 2) *
          ∑ j ∈ Finset.range n, (p * c) ^ j := by
      calc
        G x ≤ (p * c) ^ n * G (c ^ n * x) +
            Finset.sum (Finset.range n)
              (fun j ↦ (p * c) ^ j * (ε * (1 - p * c) / 2)) := hiter
        _ = (p * c) ^ n * G (c ^ n * x) +
            (ε * (1 - p * c) / 2) *
              ∑ j ∈ Finset.range n, (p * c) ^ j := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    have hterminal_nonneg : 0 ≤ c ^ n * x :=
      (mul_pos (pow_pos hc n) hx).le
    have hterminal_bdd : F (c ^ n * x) ≤ M :=
      hMbound _ hterminal_nonneg (hn_upper.trans_le (min_le_left _ _))
    have hGterminal : G (c ^ n * x) ≤ A := by
      dsimp only [G, A]
      calc
        F (c ^ n * x) / (c ^ n * x) ≤ M / (c ^ n * x) :=
          div_le_div_of_nonneg_right hterminal_bdd hterminal_nonneg
        _ ≤ M / (δ₀ / c) := by
          exact div_le_div_of_nonneg_left hM (div_pos hδ₀ hc) hn_lower
        _ = M * c / δ₀ := by field_simp
    have hqpow : (p * c) ^ n ≤ (p * c) ^ N :=
      pow_le_pow_of_le_one hq_nonneg hpc.le hNn
    have hgeom : (∑ j ∈ Finset.range n, (p * c) ^ j) ≤
        1 / (1 - p * c) := by
      apply (le_div_iff₀ (sub_pos.mpr hpc)).mpr
      rw [geom_sum_mul_neg]
      exact sub_le_self 1 (pow_nonneg hq_nonneg n)
    have hprincipal : (p * c) ^ n * G (c ^ n * x) ≤ ε / 2 := by
      calc
        (p * c) ^ n * G (c ^ n * x) ≤ (p * c) ^ n * A :=
          mul_le_mul_of_nonneg_left hGterminal (pow_nonneg hq_nonneg n)
        _ ≤ (p * c) ^ N * A := mul_le_mul_of_nonneg_right hqpow hA
        _ ≤ ((ε / 2) / (A + 1)) * A :=
          mul_le_mul_of_nonneg_right hN.le hA
        _ ≤ ε / 2 := le_of_lt <| by
          have hA_lt : A < A + 1 := lt_add_one A
          calc
            (ε / 2 / (A + 1)) * A <
                (ε / 2 / (A + 1)) * (A + 1) :=
              mul_lt_mul_of_pos_left hA_lt htarget
            _ = ε / 2 := by field_simp
    have hforcing : (ε * (1 - p * c) / 2) *
        ∑ j ∈ Finset.range n, (p * c) ^ j ≤ ε / 2 := by
      calc
        _ ≤ (ε * (1 - p * c) / 2) * (1 / (1 - p * c)) :=
          mul_le_mul_of_nonneg_left hgeom he_pos.le
        _ = ε / 2 := by
          field_simp [ne_of_gt (sub_pos.mpr hpc)]
    have hGx : G x ≤ ε := hiter'.trans <| by nlinarith
    dsimp only [G] at hGx
    exact (div_le_iff₀ hx).mp hGx

/-- A lower-equal fiber-jet variation passes linearly through a product-valued
inner jet and a scalar reindexing jet at the repeated-one top coefficient. -/
private theorem finiteTaylorJet_comp_prod_comp_topCoeff_sub_eq_linear_of_lower
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 (𝕜 × E) F m)
    (C : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (P R : FiniteTaylorJet 𝕜 𝕜 E m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = R.coeff k) :
    let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let oneM : Fin m → 𝕜 := fun _ ↦ 1
    let oneI : Fin 1 → 𝕜 := fun _ ↦ 1
    (((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff top -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I).coeff top)
      oneM) =
      ((I.coeff ⟨1, Nat.succ_lt_succ hm⟩ oneI) ^ m) •
        (continuousMultilinearCurryFin1 𝕜 (𝕜 × E) F
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
          (0, (P.coeff top - R.coeff top) oneM) := by
  classical
  -- Product formation preserves the assumed agreement at every lower order.
  have hprod_lower (k : Fin (m + 1)) (hk : (k : ℕ) < m) :
      (FiniteTaylorJet.prod C P).coeff k =
        (FiniteTaylorJet.prod C R).coeff k := by
    rw [FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod, hPR k hk]
  -- The first composition turns the fiber top gap into the stable linear branch.
  have hinner := FiniteTaylorJet.comp_topCoeff_sub_eq_inner hm Q
    (FiniteTaylorJet.prod C P) (FiniteTaylorJet.prod C R) hprod_lower
  have hinner_lower (k : Fin (m + 1)) (hk : (k : ℕ) < m) :
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff k =
        (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)).coeff k := by
    apply FiniteTaylorJet.comp_coeff_eq_of_eq_below
    · intro j _hj
      rfl
    · intro j _hj_pos hj_le
      exact hprod_lower j (hj_le.trans_lt hk)
  -- The outer scalar composition contributes the repeated first coefficient.
  have houter := FiniteTaylorJet.comp_topCoeff_sub_eq_outer
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P))
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I hinner_lower
  dsimp only
  rw [houter, FiniteTaylorJet.comp_topCoeff_outer_ones_apply,
    Composition.ones_length]
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le I
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)), hinner,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply]
  have hscale :=
    ((FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff
        ⟨m, Nat.lt_succ_self m⟩ -
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)).coeff
        ⟨m, Nat.lt_succ_self m⟩).map_smul_univ
      (fun _ : Fin m ↦ I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ ↦ 1))
      (fun _ : Fin m ↦ (1 : 𝕜))
  rw [hinner, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply] at hscale
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply] at hscale
  simp at hscale ⊢
  simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin,
    continuousMultilinearCurryFin1_apply] using hscale

namespace JetTransform

/-- Helper for Infrastructure I.16: the top coefficient of a stable jet
composition is determined by the corresponding center-stable output derivative
and the top coefficient of the input graph jet. -/
private theorem stableJet_comp_topCoeff_sub_apply_eq_directStableOutput
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {radius slope : ℝ≥0}
    (r : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (hr : 0 < r)
    (J K : BoundedGraphJet X radius slope r) (u : ℝ)
    (h_lower_coeff : ∀ k : Fin (r + 1), (k : ℕ) < r →
      (J.jet u).coeff k = (K.jet u).coeff k)
    (I : FiniteTaylorJet ℝ ℝ ℝ r) :
    (((FiniteTaylorJet.comp
        (JetTransform.stableJet r χ ρ L N J u) I).coeff
          ⟨r, Nat.lt_succ_self r⟩ -
      (FiniteTaylorJet.comp
        (JetTransform.stableJet r χ ρ L N K u) I).coeff
          ⟨r, Nat.lt_succ_self r⟩)
        (fun _ : Fin r ↦ (1 : ℝ))) =
      ((I.coeff ⟨1, Nat.succ_lt_succ hr⟩
          (fun _ : Fin 1 ↦ (1 : ℝ))) ^ r) •
        (fderiv ℝ (LocalCutoff.centerStableLinearize χ ρ L N)
          (u, J.graph u)
          (0, ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩)
              (fun _ : Fin r ↦ (1 : ℝ)))).2 := by
  have hparamCoeff (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (JetTransform.graphParametrizationJet r J u).coeff n =
        (JetTransform.graphParametrizationJet r K u).coeff n := by
    rw [JetTransform.graphParametrizationJet,
      JetTransform.graphParametrizationJet,
      FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod,
      h_lower_coeff n hn]
  have hparamConstant :
      (JetTransform.graphParametrizationJet r J u).constantCoeff =
        (JetTransform.graphParametrizationJet r K u).constantCoeff := by
    have hcoeff := hparamCoeff (0 : Fin (r + 1)) (Nat.zero_lt_of_lt hr)
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (JetTransform.graphParametrizationJet r J u).constantCoeff =
          (JetTransform.graphParametrizationJet r J u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (JetTransform.graphParametrizationJet r K u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) := hcoeffValue
      _ = (JetTransform.graphParametrizationJet r K u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  have himageCoeff (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (JetTransform.imageJet r χ ρ L N J u).coeff n =
        (JetTransform.imageJet r χ ρ L N K u).coeff n := by
    rw [JetTransform.imageJet, JetTransform.imageJet,
      FiniteTaylorJet.postcomp_def, FiniteTaylorJet.postcomp_def,
      hparamConstant]
    apply JetTransform.finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro k _
      rfl
    · intro k _ hk
      exact hparamCoeff k (hk.trans_lt hn)
  have himageConstant :
      (JetTransform.imageJet r χ ρ L N J u).constantCoeff =
        (JetTransform.imageJet r χ ρ L N K u).constantCoeff := by
    have hcoeff := himageCoeff (0 : Fin (r + 1)) (Nat.zero_lt_of_lt hr)
    have hcoeffValue := congrArg
      (fun A : ℝ [×0]→L[ℝ] (ℝ × X) ↦ A (fun _ ↦ 0)) hcoeff
    calc
      (JetTransform.imageJet r χ ρ L N J u).constantCoeff =
          (JetTransform.imageJet r χ ρ L N J u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) :=
        FiniteTaylorJet.constantCoeff_eq_coeff_zero _
      _ = (JetTransform.imageJet r χ ρ L N K u).coeff
            (0 : Fin (r + 1)) (fun _ ↦ 0) := hcoeffValue
      _ = (JetTransform.imageJet r χ ρ L N K u).constantCoeff :=
        (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
  have hstableCoeff (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (JetTransform.stableJet r χ ρ L N J u).coeff n =
        (JetTransform.stableJet r χ ρ L N K u).coeff n := by
    rw [JetTransform.stableJet, JetTransform.stableJet,
      FiniteTaylorJet.postcomp_def, FiniteTaylorJet.postcomp_def,
      himageConstant]
    apply JetTransform.finiteTaylorJet_comp_coeff_eq_of_eq_below
    · intro k _
      rfl
    · intro k _ hk
      exact himageCoeff k (hk.trans_lt hn)
  have houter := JetTransform.finiteTaylorJet_comp_topCoeff_sub_eq_outer
    (JetTransform.stableJet r χ ρ L N J u)
    (JetTransform.stableJet r χ ρ L N K u) I hstableCoeff
  rw [houter, finiteTaylorJet_comp_topCoeff_outer_ones_apply,
    Composition.ones_length]
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (JetTransform.stableJet r χ ρ L N J u) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (JetTransform.stableJet r χ ρ L N K u) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le I
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr))]
  have hstableTop :
      (JetTransform.stableJet r χ ρ L N J u).coeff
          ⟨r, Nat.lt_succ_self r⟩ -
        (JetTransform.stableJet r χ ρ L N K u).coeff
          ⟨r, Nat.lt_succ_self r⟩ =
      (continuousMultilinearCurryFin1 ℝ (ℝ × X) X
        ((FiniteTaylorJet.ofFunction ℝ r Prod.snd
          (JetTransform.imageJet r χ ρ L N J u).constantCoeff).coeff
            ⟨1, Nat.succ_lt_succ hr⟩)).compContinuousMultilinearMap
        ((JetTransform.imageJet r χ ρ L N J u).coeff
          ⟨r, Nat.lt_succ_self r⟩ -
          (JetTransform.imageJet r χ ρ L N K u).coeff
            ⟨r, Nat.lt_succ_self r⟩) := by
    rw [JetTransform.stableJet, JetTransform.stableJet,
      FiniteTaylorJet.postcomp_def, FiniteTaylorJet.postcomp_def,
      himageConstant]
    exact JetTransform.finiteTaylorJet_comp_topCoeff_sub_eq_inner hr _ _ _ himageCoeff
  have himageTop :
      (JetTransform.imageJet r χ ρ L N J u).coeff
          ⟨r, Nat.lt_succ_self r⟩ -
        (JetTransform.imageJet r χ ρ L N K u).coeff
          ⟨r, Nat.lt_succ_self r⟩ =
      (continuousMultilinearCurryFin1 ℝ (ℝ × X) (ℝ × X)
        ((FiniteTaylorJet.ofFunction ℝ r
          (LocalCutoff.centerStableLinearize χ ρ L N)
          (JetTransform.graphParametrizationJet r J u).constantCoeff).coeff
            ⟨1, Nat.succ_lt_succ hr⟩)).compContinuousMultilinearMap
        ((JetTransform.graphParametrizationJet r J u).coeff
          ⟨r, Nat.lt_succ_self r⟩ -
          (JetTransform.graphParametrizationJet r K u).coeff
            ⟨r, Nat.lt_succ_self r⟩) := by
    rw [JetTransform.imageJet, JetTransform.imageJet,
      FiniteTaylorJet.postcomp_def, FiniteTaylorJet.postcomp_def,
      hparamConstant]
    exact JetTransform.finiteTaylorJet_comp_topCoeff_sub_eq_inner hr _ _ _ hparamCoeff
  have hparamTopValue (z : Fin r → ℝ) :
      ((JetTransform.graphParametrizationJet r J u).coeff
          ⟨r, Nat.lt_succ_self r⟩ -
        (JetTransform.graphParametrizationJet r K u).coeff
          ⟨r, Nat.lt_succ_self r⟩) z =
      (0, ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
        (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z) := by
    rw [JetTransform.graphParametrizationJet,
      JetTransform.graphParametrizationJet,
      FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod]
    change
      ((FiniteTaylorJet.ofFunction ℝ r id u).coeff
            ⟨r, Nat.lt_succ_self r⟩ z -
        (FiniteTaylorJet.ofFunction ℝ r id u).coeff
            ⟨r, Nat.lt_succ_self r⟩ z,
        (J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ z -
          (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ z) = _
    rw [sub_self]
    rfl
  have hparamBase :
      (JetTransform.graphParametrizationJet r J u).constantCoeff =
        (u, J.graph u) := by
    rw [JetTransform.graphParametrizationJet,
      JetTransform.finiteTaylorJet_constantCoeff_prod,
      FiniteTaylorJet.constantCoeff_ofFunction, J.constantCoeff_eq]
    rfl
  have hstableTopValue (z : Fin r → ℝ) :
      ((JetTransform.stableJet r χ ρ L N J u).coeff
          ⟨r, Nat.lt_succ_self r⟩ -
        (JetTransform.stableJet r χ ρ L N K u).coeff
          ⟨r, Nat.lt_succ_self r⟩) z =
        (fderiv ℝ (LocalCutoff.centerStableLinearize χ ρ L N)
          (u, J.graph u)
          (0, ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) z)).2 := by
    rw [hstableTop, ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply, himageTop,
      ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply, hparamTopValue, hparamBase]
    rw [continuousMultilinearCurryFin1_apply,
      FiniteTaylorJet.coeff_ofFunction_apply]
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_one_apply, fderiv_snd, ContinuousLinearMap.coe_snd',
      Fin.snoc_zero]
    rw [continuousMultilinearCurryFin1_apply,
      FiniteTaylorJet.coeff_ofFunction_apply]
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_one_apply, fderiv_snd, ContinuousLinearMap.coe_snd',
      Fin.snoc_zero]
  let scalarTop : ℝ :=
    I.coeff ⟨1, Nat.succ_lt_succ hr⟩ (fun _ : Fin 1 ↦ (1 : ℝ))
  have hscale :=
    ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
      (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩).map_smul_univ
      (fun _ : Fin r ↦ scalarTop) (fun _ : Fin r ↦ (1 : ℝ))
  have hscale' :
      ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
        (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩)
          (fun _ : Fin r ↦ scalarTop) =
        (scalarTop ^ r) •
          ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩)
            (fun _ : Fin r ↦ (1 : ℝ)) := by
    simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin]
      using hscale
  rw [hstableTopValue, hscale']
  have hpair_smul :
      ((0 : ℝ), scalarTop ^ r •
          ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩)
            (fun _ : Fin r ↦ (1 : ℝ))) =
        scalarTop ^ r •
          ((0 : ℝ), ((J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
            (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩)
            (fun _ : Fin r ↦ (1 : ℝ))) := by
    rw [Prod.smul_mk, smul_zero]
  rw [hpair_smul, map_smul]
  rfl

end JetTransform

/-- An additive decomposition transfers separate norm bounds to the decomposed
vector. -/
private theorem norm_le_of_eq_add_of_norm_le
    {E : Type*} [NormedAddCommGroup E]
    {x y z : E} {A B : ℝ}
    (hdecomp : x = y + z) (hy : ‖y‖ ≤ A) (hz : ‖z‖ ≤ B) :
    ‖x‖ ≤ A + B := by
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add hy hz)

/-- Evaluation of a bounded multilinear section at a fixed base point and
    fixed source vector preserves convergence in the uniform-function norm. -/
private theorem tendsto_bounded_multilinearSection_eval
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {r : ℕ}
    (sections : ℝ → BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y))
    (limitSection : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y))
    (u : ℝ) (w : Fin r → ℝ)
    (hsections : Tendsto sections (𝓝 0) (𝓝 limitSection)) :
    Tendsto (fun t : ℝ => (sections t u) w) (𝓝 0) (𝓝 ((limitSection u) w)) := by
  -- First evaluate the bounded function at the base point, then evaluate the
  -- resulting multilinear map; each map is continuous in its argument.
  have hsection_u : Tendsto (fun t : ℝ => sections t u)
      (𝓝 0) (𝓝 (limitSection u)) := by
    exact ((BoundedContinuousFunction.lipschitz_eval_const u).continuous.continuousAt.tendsto).comp
      hsections
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => ℝ) Y w).continuous.continuousAt.tendsto).comp
    hsection_u

/-- A factorial-normalized bounded section secant identifies the derivative of
    a scalar-source predecessor coefficient.  The construction of the
    sections and their convergence is deliberately left to the graph-jet
    endpoint argument; this lemma only performs the final derivative bridge. -/
private theorem hasDerivAt_of_factorial_section_secant
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {r : ℕ} (f : ℝ → Y)
    (sections : ℝ → BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y))
    (limitSection : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y))
    (oneTop : Fin r → ℝ)
    (hsections : Tendsto sections (𝓝 0) (𝓝 limitSection))
    (hsecant : ∀ u : ℝ,
      (fun t : ℝ => t⁻¹ • (f (u + t) - f u)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
        (fun t => (r.factorial : ℝ) • (sections t u) oneTop)) :
    ∀ u, HasDerivAt f
      ((r.factorial : ℝ) • (limitSection u) oneTop) u := by
  -- Evaluate first at the base point and then at the multilinear all-ones
  -- vector; both evaluations are continuous, so the bounded-section bridge
  -- applies without changing the section's natural graph-jet type.
  intro u
  have heval_top : Tendsto (fun t : ℝ => (sections t u) oneTop)
      (𝓝 0) (𝓝 ((limitSection u) oneTop)) :=
    tendsto_bounded_multilinearSection_eval sections limitSection u oneTop hsections
  exact hasDerivAt_of_tendsto_slope_smul
    f u (r.factorial : ℝ) (fun t : ℝ => (sections t u) oneTop)
    ((limitSection u) oneTop) heval_top (hsecant u)

/-- Helper for Infrastructure I.16a: a sublinear radius envelope forces a
    bounded section to converge whenever its nonzero distance is controlled by
    the normalized envelope. -/
private theorem tendsto_boundedSection_of_radiusEnvelope
    {Z : Type*} [NormedAddCommGroup Z]
    (sections : ℝ → BoundedContinuousFunction ℝ Z)
    (limitSection : BoundedContinuousFunction ℝ Z)
    (F : ℝ → ℝ) (A p c : ℝ)
    (hA : 0 ≤ A)
    (hmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hp : 0 ≤ p) (hp_lt : p < 1) (hc : 0 < c) (hpc : p * c < 1)
    (hbounded : ∃ δ > 0, ∃ M ≥ 0, ∀ x, 0 ≤ x → x < δ → F x ≤ M)
    (hrec : ∀ e > 0, ∃ δ > 0, ∀ x, 0 < x → x < δ →
      F x ≤ p * F (c * x) + e * x)
    (hdist : ∀ t, t ≠ 0 →
      dist (sections t) limitSection ≤ A * ‖t⁻¹‖ * F ‖t‖)
    (hzero : sections 0 = limitSection) :
    Tendsto sections (𝓝 0) (𝓝 limitSection) := by
  have hsublinear := radiusEnvelope_sublinear_of_localRecurrence F p c
    hmono hp hp_lt hc hpc hbounded hrec
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_cases hA_zero : A = 0
  · refine Filter.Eventually.of_forall ?_
    intro t
    by_cases ht : t = 0
    · subst t
      rw [hzero, dist_self]
      exact hε
    · have hbound := hdist t ht
      have hbound' : dist (sections t) limitSection ≤ 0 := by
        simpa only [hA_zero, zero_mul] using hbound
      exact lt_of_le_of_lt hbound' hε
  · have hA_pos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA_zero)
    have hεA : 0 < ε / (2 * A) := by positivity
    obtain ⟨δ, hδ, hF⟩ := hsublinear (ε / (2 * A)) hεA
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    by_cases ht_zero : t = 0
    · subst t
      rw [hzero, dist_self]
      exact hε
    · have ht_norm_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht_zero
      have ht_norm_lt : ‖t‖ < δ := by
        simpa only [Metric.mem_ball, dist_zero_right] using ht
      have hF_t := hF ‖t‖ ht_norm_pos ht_norm_lt
      have hcoef_nonneg : 0 ≤ A * ‖t⁻¹‖ :=
        mul_nonneg hA (norm_nonneg _)
      calc
        dist (sections t) limitSection ≤ A * ‖t⁻¹‖ * F ‖t‖ := hdist t ht_zero
        _ ≤ A * ‖t⁻¹‖ * ((ε / (2 * A)) * ‖t‖) :=
          mul_le_mul_of_nonneg_left hF_t hcoef_nonneg
        _ = ε / 2 := by
          have hnorm : ‖t⁻¹‖ * ‖t‖ = 1 := by
            rw [← norm_mul, inv_mul_cancel₀ ht_zero, norm_one]
          calc
            A * ‖t⁻¹‖ * ((ε / (2 * A)) * ‖t‖) =
                (ε / (2 * A)) * (A * (‖t⁻¹‖ * ‖t‖)) := by ring
            _ = ε / 2 := by
              rw [hnorm]
              field_simp [hA_pos.ne']
        _ < ε := half_lt_self hε

/-- An explicitly typed bounded-section convergence adapter for scalar-source
    multilinear sections. -/
private theorem tendsto_boundedMultilinearSection_of_radiusEnvelope
    {Z : Type*} [NormedAddCommGroup Z]
    (sections : ℝ → BoundedContinuousFunction ℝ Z)
    (limitSection : BoundedContinuousFunction ℝ Z)
    (F : ℝ → ℝ) (A p c : ℝ)
    (hA : 0 ≤ A)
    (hmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hp : 0 ≤ p) (hp_lt : p < 1) (hc : 0 < c) (hpc : p * c < 1)
    (hbounded : ∃ δ > 0, ∃ M ≥ 0, ∀ x, 0 ≤ x → x < δ → F x ≤ M)
    (hrec : ∀ e > 0, ∃ δ > 0, ∀ x, 0 < x → x < δ →
      F x ≤ p * F (c * x) + e * x)
    (hdist : ∀ t, t ≠ 0 →
      dist (sections t) limitSection ≤ A * ‖t⁻¹‖ * F ‖t‖)
    (hzero : sections 0 = limitSection) :
    Tendsto sections (𝓝 0) (𝓝 limitSection) := by
  -- Pin the codomain before invoking the existing envelope convergence theorem.
  exact tendsto_boundedSection_of_radiusEnvelope sections limitSection F A p c hA
    hmono hp hp_lt hc hpc hbounded hrec hdist hzero

/-- The radius-envelope convergence theorem specialized to multilinear section
    codomains, with all carrier instances fixed at the declaration boundary. -/
private theorem tendsto_multilinearSection_of_radiusEnvelope_explicit
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {r : ℕ}
    (sections : ℝ → BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (limitSection : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (F : ℝ → ℝ) (A p c : ℝ)
    (hA : 0 ≤ A)
    (hmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hp : 0 ≤ p) (hp_lt : p < 1) (hc : 0 < c) (hpc : p * c < 1)
    (hbounded : ∃ δ > 0, ∃ M ≥ 0, ∀ x, 0 ≤ x → x < δ → F x ≤ M)
    (hrec : ∀ e > 0, ∃ δ > 0, ∀ x, 0 < x → x < δ →
      F x ≤ p * F (c * x) + e * x)
    (hdist : ∀ t, t ≠ 0 →
      dist (sections t) limitSection ≤ A * ‖t⁻¹‖ * F ‖t‖)
    (hzero : sections 0 = limitSection) :
    Tendsto sections (𝓝 0) (𝓝 limitSection) := by
  -- The fully instantiated adapter leaves only ordinary scalar arguments in
  -- the calling theorem.
  exact tendsto_boundedMultilinearSection_of_radiusEnvelope
    sections limitSection F A p c hA hmono hp hp_lt hc hpc hbounded hrec hdist hzero

/-- Every coefficient of a finite Taylor jet vanishes at a point outside the
    topological support of its underlying function. -/
private theorem finiteTaylorJet_ofFunction_coeff_zero_of_notMem_tsupport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (f : E → F) (x : E) (hx : x ∉ tsupport f)
    (n : Fin (m + 1)) :
    (FiniteTaylorJet.ofFunction ℝ m f x).coeff n = 0 := by
  -- The coefficient is a factorial-scaled iterated derivative; support
  -- exclusion forces that derivative to vanish at the same point.
  rw [FiniteTaylorJet.coeff_ofFunction]
  have hderiv_zero : iteratedFDeriv ℝ (n : ℕ) f x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hmem => hx
      (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) (n : ℕ) hmem)
  rw [hderiv_zero, smul_zero]

/-- Helper for Infrastructure I.16: composing a top-truncated finite jet with
the identity has zero top coefficient. -/
private theorem topCoeff_truncateTopCoeff_comp_identity_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (r : ℕ) (S : FiniteTaylorJet ℝ ℝ X r) (z : ℝ) :
    (FiniteTaylorJet.comp (truncateTopCoeff S)
      (FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z)).coeff
        ⟨r, Nat.lt_succ_self r⟩ = 0 := by
  -- Higher identity coefficients vanish, so every non-all-ones branch has a
  -- zero inner factor; the all-ones branch sees the truncated top coefficient.
  have hid_coeff_zero_of_one_lt (k : Fin (r + 1))
      (hk : 1 < (k : ℕ)) :
      (FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z).coeff k = 0 := by
    rw [FiniteTaylorJet.coeff_ofFunction]
    have hiter : iteratedDeriv (k : ℕ) (id : ℝ → ℝ) z = 0 := by
      rw [iteratedDeriv_id]
      have hk0 : (k : ℕ) ≠ 0 := by omega
      have hk1 : (k : ℕ) ≠ 1 := by omega
      simp only [hk0, hk1, if_false]
    have hiterF_apply :
        (iteratedFDeriv ℝ (k : ℕ) (id : ℝ → ℝ) z) (fun _ ↦ (1 : ℝ)) = 0 := by
      simpa only [iteratedDeriv_eq_iteratedFDeriv] using hiter
    have hiterF : iteratedFDeriv ℝ (k : ℕ) (id : ℝ → ℝ) z = 0 := by
      calc
        iteratedFDeriv ℝ (k : ℕ) (id : ℝ → ℝ) z =
            ContinuousMultilinearMap.mkPiRing ℝ (Fin (k : ℕ))
              ((iteratedFDeriv ℝ (k : ℕ) (id : ℝ → ℝ) z)
                (fun _ ↦ (1 : ℝ))) :=
          (ContinuousMultilinearMap.mkPiRing_apply_one_eq_self _).symm
        _ = 0 := by rw [hiterF_apply, ContinuousMultilinearMap.mkPiRing_zero]
    rw [hiterF, smul_zero]
  have hones_zero :
      (truncateTopCoeff S).toFormalMultilinearSeries.compAlongComposition
          (FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z).toFormalMultilinearSeries
          (Composition.ones r) = 0 := by
    let F := (truncateTopCoeff S).toFormalMultilinearSeries.compAlongComposition
      (FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z).toFormalMultilinearSeries
      (Composition.ones r)
    have hones_len : (Composition.ones r).length = r :=
      Composition.ones_length r
    have htop_r : (truncateTopCoeff S).toFormalMultilinearSeries r = 0 := by
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
        (truncateTopCoeff S) le_rfl]
      rw [truncateTopCoeff, FiniteTaylorJet.replaceTopCoeff_coeff_top]
    have htop : (truncateTopCoeff S).toFormalMultilinearSeries
        (Composition.ones r).length = 0 := by
      rw [hones_len]
      exact htop_r
    have hone_eval : F (fun _ : Fin r ↦ (1 : ℝ)) = 0 := by
      dsimp only [F]
      rw [FormalMultilinearSeries.compAlongComposition_apply]
      rw [htop]
      simp
    calc
      F = ContinuousMultilinearMap.mkPiRing ℝ (Fin r)
          (F (fun _ : Fin r ↦ (1 : ℝ))) :=
        (ContinuousMultilinearMap.mkPiRing_apply_one_eq_self F).symm
      _ = 0 := by rw [hone_eval, ContinuousMultilinearMap.mkPiRing_zero]
  have hbranch_zero (c : Composition r)
      (hc : c ≠ Composition.ones r) :
      ((truncateTopCoeff S).toFormalMultilinearSeries.compAlongComposition
          (FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z).toFormalMultilinearSeries c) = 0 := by
    have hlength_ne : (c.length : ℕ) ≠ r := by
      intro hlength
      exact hc (Composition.eq_ones_iff_length.mpr hlength)
    have hlength_lt : (c.length : ℕ) < r :=
      lt_of_le_of_ne c.length_le hlength_ne
    have hblock : ∃ i : Fin c.length, 1 < c.blocksFun i := by
      by_contra hnone
      have hblock_le : ∀ i : Fin c.length, c.blocksFun i ≤ 1 := by
        intro i
        exact Nat.le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
      have hsum_le : (∑ i : Fin c.length, c.blocksFun i) ≤
          ∑ _ : Fin c.length, 1 := by
        exact Finset.sum_le_sum (fun i _ => hblock_le i)
      have hlength_ge : r ≤ (c.length : ℕ) := by
        simpa [c.sum_blocksFun] using hsum_le
      exact (Nat.not_le_of_lt hlength_lt) hlength_ge
    obtain ⟨i, hi⟩ := hblock
    have hblock_le_r : c.blocksFun i ≤ r := c.blocksFun_le i
    have hblock_lt_succ : c.blocksFun i < r + 1 :=
      lt_of_le_of_lt hblock_le_r (Nat.lt_succ_self r)
    have hblock_zero :
        (FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z).toFormalMultilinearSeries
            (c.blocksFun i) = 0 := by
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
        (FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z) hblock_le_r]
      exact hid_coeff_zero_of_one_lt
        ⟨c.blocksFun i, hblock_lt_succ⟩ hi
    ext w
    rw [FormalMultilinearSeries.compAlongComposition_apply]
    apply ContinuousMultilinearMap.map_coord_zero _ i
    dsimp only [FormalMultilinearSeries.applyComposition]
    rw [hblock_zero, _root_.zero_apply]
  rw [JetTransform.finiteTaylorJet_comp_topCoeff_branch_split]
  rw [hones_zero, zero_add]
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hones : c = Composition.ones r
  · simp only [if_pos hones]
  · simp only [if_neg hones]
    exact hbranch_zero c hones

/-- A local raw-defect recurrence lifts to the corresponding supremum-envelope
   recurrence.  Keeping this generic avoids re-elaborating the set supremum
   argument inside the finite-order graph-transform theorem. -/
private theorem defectEnvelope_recurrence_of_rawRecurrence
    {X : Type u} [NormedAddCommGroup X]
    (raw : ℝ → ℝ → X) (inverse : ℝ → ℝ)
    (p c η : ℝ) (defectRange : ℝ → Set ℝ) (defectEnvelope : ℝ → ℝ)
    (hdefectRange_mem : ∀ y z, z ∈ defectRange y ↔
      ∃ u h : ℝ, ‖h‖ ≤ y ∧ z = ‖raw u h‖)
    (hdefectRange_nonempty : ∀ {y : ℝ}, 0 ≤ y → (defectRange y).Nonempty)
    (hdefectRange_bdd : ∀ {y : ℝ}, 0 ≤ y → BddAbove (defectRange y))
    (hdefectEnvelope_eq : ∀ y, defectEnvelope y = sSup (defectRange y))
    (hdefectEnvelope_nonneg : ∀ {y : ℝ}, 0 ≤ y → 0 ≤ defectEnvelope y)
    (hraw_zero : ∀ u, raw u 0 = 0)
    (hη_nonneg : 0 ≤ η)
    (hp_nonneg : 0 ≤ p) (hc_pos : 0 < c)
    (hinverse_increment_norm_le : ∀ u s,
      ‖inverse (u + s) - inverse u‖ ≤ c * ‖s‖)
    (hraw_recurrence : ∃ δ > 0, ∀ u s, s ≠ 0 → ‖s‖ < δ →
      ‖raw u s‖ ≤
        p * ‖raw (inverse u) (inverse (u + s) - inverse u)‖ + η * ‖s‖) :
    ∃ δ > 0, ∀ y, 0 < y → y < δ →
      defectEnvelope y ≤ p * defectEnvelope (c * y) + η * y := by
  -- Transfer the raw recurrence to each element of the envelope range.
  obtain ⟨δ, hδ, hrec⟩ := hraw_recurrence
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyδ
  rw [hdefectEnvelope_eq]
  apply csSup_le (hdefectRange_nonempty hy.le)
  intro z hz
  obtain ⟨u, s, hs, rfl⟩ := (hdefectRange_mem y z).mp hz
  -- The zero increment is handled by envelope nonnegativity; nonzero
  -- increments are reindexed through the inverse map and bounded by `hΔ`.
  by_cases hs_zero : s = 0
  · subst s
    rw [hraw_zero, norm_zero]
    exact add_nonneg
      (mul_nonneg hp_nonneg (hdefectEnvelope_nonneg (mul_nonneg hc_pos.le hy.le)))
      (mul_nonneg hη_nonneg hy.le)
  · have hsδ : ‖s‖ < δ := hs.trans_lt hyδ
    have hΔ : ‖inverse (u + s) - inverse u‖ ≤ c * y := by
      calc
        ‖inverse (u + s) - inverse u‖ ≤ c * ‖s‖ :=
          hinverse_increment_norm_le u s
        _ ≤ c * y := mul_le_mul_of_nonneg_left hs hc_pos.le
    have hΔEnvelope :
        ‖raw (inverse u) (inverse (u + s) - inverse u)‖ ≤
          defectEnvelope (c * y) := by
      rw [hdefectEnvelope_eq]
      apply le_csSup (hdefectRange_bdd (mul_nonneg hc_pos.le hy.le))
      apply (hdefectRange_mem (c * y)
        (‖raw (inverse u) (inverse (u + s) - inverse u)‖)).mpr
      exact ⟨inverse u, inverse (u + s) - inverse u, hΔ, rfl⟩
    calc
      ‖raw u s‖ ≤
          p * ‖raw (inverse u) (inverse (u + s) - inverse u)‖ + η * ‖s‖ :=
        hrec u s hs_zero hsδ
      _ ≤ p * defectEnvelope (c * y) + η * y :=
        add_le_add
          (mul_le_mul_of_nonneg_left hΔEnvelope hp_nonneg)
          (mul_le_mul_of_nonneg_left hs hη_nonneg)

/-- Helper for Infrastructure I.16: a filtered endpoint residual gives the exact
projected affine identity in output coordinates.  The principal operator is
evaluated at `u`, while its recursive defect is evaluated at the inverse source
`inverse u` with increment `inverse (u + s) - inverse u`; the filtered endpoint
term remains the difference between the output endpoints `u` and `u + s`. -/
private theorem rawDefect_eq_projectedPrincipal_add_filteredEndpointResidual
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (r : ℕ) (rawDefect : ℝ → ℝ → X) (inverse : ℝ → ℝ)
    (principalOperator : ℝ → X →L[ℝ] X)
    (filteredEndpoint : ℝ → (ℝ [×r]→L[ℝ] X))
    (oneTop : Fin r → ℝ) (u s : ℝ)
    (hfiltered :
      rawDefect u s -
          principalOperator u
            (rawDefect (inverse u) (inverse (u + s) - inverse u)) =
        (r.factorial : ℝ) •
          (s • ((filteredEndpoint u - filteredEndpoint (u + s))
            oneTop))) :
    rawDefect u s =
      principalOperator u
          (rawDefect (inverse u) (inverse (u + s) - inverse u)) +
        (r.factorial : ℝ) •
          (s • ((filteredEndpoint u - filteredEndpoint (u + s))
            oneTop)) := by
  rw [sub_eq_iff_eq_add] at hfiltered
  exact hfiltered.trans (add_comm _ _)

/-- The factorial-normalized secant of a scalar derivative has a direct additive
   normal form.  This keeps nested scalar actions out of the graph-transform
   theorem's already large elaboration context. -/
private theorem normalized_sub_factorial_smul
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (r : ℕ) (t : ℝ) (ht : t ≠ 0) (A B C : X) :
    (r.factorial : ℝ)⁻¹ • t⁻¹ •
          (A - B - t • ((r.factorial : ℝ) • C)) =
      (r.factorial : ℝ)⁻¹ • t⁻¹ • (A - B) - C := by
  -- Normalize the scalar actions and cancel the nonzero secant factors.
  rw [smul_sub, smul_sub, smul_smul]
  have hfactorial : (r.factorial : ℝ) ≠ 0 := by positivity
  have hscalar :
      (r.factorial : ℝ)⁻¹ * (t⁻¹ * (t * (r.factorial : ℝ))) = 1 := by
    field_simp [ht, hfactorial]
  simp only [smul_smul, hscalar, one_smul]

/-- Helper for Infrastructure I.16: a bounded continuous scalar-source map has canonical
factorial-normalized multilinear secant sections.  Away from the zero increment their
all-ones evaluation is exactly the normalized secant, while at zero the prescribed limit
section is used. -/
private theorem exists_factorialNormalizedSecantSections
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {r : ℕ} (f : ℝ → Y) (hf : Continuous f)
    (C : ℝ) (hf_bound : ∀ u, ‖f u‖ ≤ C)
    (limitSection : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y)) :
    ∃ sections : ℝ → BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y),
      sections 0 = limitSection ∧
        (∀ t, t ≠ 0 → ∀ u,
          (sections t u) (fun _ : Fin r ↦ (1 : ℝ)) =
            (r.factorial : ℝ)⁻¹ •
              (t⁻¹ • (f (u + t) - f u))) ∧
        (∀ t, t ≠ 0 → ∀ u,
          ‖sections t u - limitSection u‖ =
            ‖(r.factorial : ℝ)⁻¹ •
                (t⁻¹ • (f (u + t) - f u)) -
              limitSection u (fun _ : Fin r ↦ (1 : ℝ))‖) ∧
        ∀ u : ℝ,
          (fun t : ℝ ↦ t⁻¹ • (f (u + t) - f u)) =ᶠ[
              nhdsWithin 0 ({0}ᶜ : Set ℝ)]
            (fun t ↦ (r.factorial : ℝ) •
              (sections t u) (fun _ : Fin r ↦ (1 : ℝ))) := by
  let topDifference (t u : ℝ) : ℝ [×r]→L[ℝ] Y :=
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) Y)
      ((r.factorial : ℝ)⁻¹ •
        (t⁻¹ • (f (u + t) - f u)))
  have htopDifference_apply_one (t u : ℝ) :
      topDifference t u (fun _ : Fin r ↦ (1 : ℝ)) =
        (r.factorial : ℝ)⁻¹ •
          (t⁻¹ • (f (u + t) - f u)) := by
    dsimp only [topDifference]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) Y).symm_apply_apply _
  have htopDifference_continuous (t : ℝ) :
      Continuous (topDifference t) := by
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) Y).continuous.comp
      (continuous_const.smul (continuous_const.smul
        ((hf.comp (continuous_id.add continuous_const)).sub hf)))
  have htopDifference_norm_le (t u : ℝ) :
      ‖topDifference t u‖ ≤
        ‖(r.factorial : ℝ)⁻¹‖ * ‖t⁻¹‖ * (2 * C) := by
    have hsub : ‖f (u + t) - f u‖ ≤ 2 * C := by
      calc
        ‖f (u + t) - f u‖ ≤ ‖f (u + t)‖ + ‖f u‖ :=
          norm_sub_le _ _
        _ ≤ C + C := add_le_add (hf_bound _) (hf_bound _)
        _ = 2 * C := by ring
    calc
      ‖topDifference t u‖ =
          ‖(r.factorial : ℝ)⁻¹ •
            (t⁻¹ • (f (u + t) - f u))‖ :=
        LinearIsometryEquiv.norm_map _ _
      _ = ‖(r.factorial : ℝ)⁻¹‖ * ‖t⁻¹‖ *
          ‖f (u + t) - f u‖ := by
        rw [norm_smul, norm_smul, mul_assoc]
      _ ≤ ‖(r.factorial : ℝ)⁻¹‖ * ‖t⁻¹‖ * (2 * C) :=
        mul_le_mul_of_nonneg_left hsub
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  let rawSecantSection (t : ℝ) :
      BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y) :=
    BoundedContinuousFunction.ofNormedAddCommGroup (topDifference t)
      (htopDifference_continuous t)
      (‖(r.factorial : ℝ)⁻¹‖ * ‖t⁻¹‖ * (2 * C))
      (htopDifference_norm_le t)
  let sections (t : ℝ) :
      BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] Y) :=
    if t = 0 then limitSection else rawSecantSection t
  have hsections_zero : sections 0 = limitSection := by
    simp only [sections, if_pos]
  have hsections_apply_one (t : ℝ) (ht : t ≠ 0) (u : ℝ) :
      (sections t u) (fun _ : Fin r ↦ (1 : ℝ)) =
        (r.factorial : ℝ)⁻¹ •
          (t⁻¹ • (f (u + t) - f u)) := by
    simp only [sections, ht, if_false, rawSecantSection,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    exact htopDifference_apply_one t u
  have hscalarSourceNormEqApplyOne
      (A B : ℝ [×r]→L[ℝ] Y) :
      ‖A - B‖ = ‖(A - B) (fun _ : Fin r ↦ (1 : ℝ))‖ := by
    calc
      ‖A - B‖ =
          ‖(ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) Y).symm
            (A - B)‖ := by
        rw [LinearIsometryEquiv.norm_map]
      _ = ‖(A - B) (fun _ : Fin r ↦ (1 : ℝ))‖ := by
        congr 1
  have hsections_distance (t : ℝ) (ht : t ≠ 0) (u : ℝ) :
      ‖sections t u - limitSection u‖ =
        ‖(r.factorial : ℝ)⁻¹ •
            (t⁻¹ • (f (u + t) - f u)) -
          limitSection u (fun _ : Fin r ↦ (1 : ℝ))‖ := by
    rw [hscalarSourceNormEqApplyOne, sub_apply]
    rw [hsections_apply_one t ht u]
  refine ⟨sections, hsections_zero, hsections_apply_one, hsections_distance, ?_⟩
  intro u
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_ne : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  rw [hsections_apply_one t ht_ne u, smul_smul]
  have hfactorial_ne : (r.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero r)
  rw [mul_inv_cancel₀ hfactorial_ne, one_smul]

set_option maxHeartbeats 1000000 in
-- The successor proof assembles both high-order and order-one certificates.
/-- Infrastructure I.16 (Finite-order graph-jet contraction): finite-order bunching
upgrades a `C^(r - 1)` fixed graph of the cutoff graph transform to a `C^r` graph. -/
theorem contDiff_succ_of_fixedPoint (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hr_pos : 1 ≤ r) (hrν : r ≤ ν)
    (hχ_smooth : ContDiff ℝ ν χ) (hχ_support : HasCompactSupport χ)
    (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_linearRate : linearRate < 1)
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_center_fiber : ∀ u : ℝ, ∀ z w : X,
      |(LocalCutoff.remainder χ ρ N (u, z)).1 -
          (LocalCutoff.remainder χ ρ N (u, w)).1| ≤
        (centerFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (h_rate : rate lower linearRate stableCenter stableFiber centerFiber slope < 1)
    (h_bunching : rate lower linearRate stableCenter stableFiber centerFiber slope *
      lower⁻¹ ^ r < 1)
    (ζ : SmallLipschitzGraph X radius slope) (hζ_prev : ContDiff ℝ (r - 1) ζ)
    (hζ_fixed : map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz
      h_radius h_slope ζ = ζ) :
    ContDiff ℝ r ζ := by
  -- Record the positive order in the strict form used by top-coefficient updates.
  have hr_strict : 0 < r := by omega
  -- The fixed-point equality first yields the invariant graph equation after
  -- evaluating both bundled graphs at an arbitrary center parameter.
  have hfixed_apply (u : ℝ) :
      ζ u =
        (LocalCutoff.centerStableLinearize χ ρ L N
          (LocalCutoff.CenterProjection.inverse χ ρ L N ζ u,
            ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ u))).2 := by
    have hpoint := congrArg (fun η : SmallLipschitzGraph X radius slope ↦ η u) hζ_fixed
    rw [map_apply] at hpoint
    exact hpoint.symm
  have hν_ne : ν ≠ 0 := by omega
  have hcenter_differentiable (η : SmallLipschitzGraph X radius slope) :
      Differentiable ℝ (LocalCutoff.CenterProjection.map χ ρ L N η) :=
    (h_center_smooth η).differentiable (Nat.cast_ne_zero.mpr hν_ne)
  have hcenter_bijective (η : SmallLipschitzGraph X radius slope) :
      Function.Bijective (LocalCutoff.CenterProjection.map χ ρ L N η) :=
    Real.bijective_of_pos_le_deriv (hcenter_differentiable η) h_lower_pos (h_lower η)
  -- The derivative lower bound gives the quantitative inverse scale needed
  -- after normalizing predecessor secants by the original increment.
  have hcenter_inverse_lipschitz (η : SmallLipschitzGraph X radius slope) :
      LipschitzWith lower⁻¹ (LocalCutoff.CenterProjection.inverse χ ρ L N η) := by
    rw [LocalCutoff.CenterProjection.inverse_def]
    exact Real.lipschitzWith_invFun_of_pos_le_deriv
      (hcenter_differentiable η) h_lower_pos (h_lower η)
  have hinverse_reindexedIncrement_norm_le (u t : ℝ) :
      ‖(LocalCutoff.CenterProjection.inverse χ ρ L N ζ)
          (LocalCutoff.CenterProjection.map χ ρ L N ζ u + t) - u‖ ≤
        (lower⁻¹ : ℝ) * ‖t‖ := by
    have hinverse_map :
        LocalCutoff.CenterProjection.inverse χ ρ L N ζ
            (LocalCutoff.CenterProjection.map χ ρ L N ζ u) = u := by
      rw [LocalCutoff.CenterProjection.inverse_def]
      exact Function.leftInverse_invFun (hcenter_bijective ζ).1 u
    calc
      ‖(LocalCutoff.CenterProjection.inverse χ ρ L N ζ)
          (LocalCutoff.CenterProjection.map χ ρ L N ζ u + t) - u‖ =
          dist ((LocalCutoff.CenterProjection.inverse χ ρ L N ζ)
            (LocalCutoff.CenterProjection.map χ ρ L N ζ u + t))
            ((LocalCutoff.CenterProjection.inverse χ ρ L N ζ)
              (LocalCutoff.CenterProjection.map χ ρ L N ζ u)) := by
        rw [Real.dist_eq, hinverse_map, Real.norm_eq_abs]
      _ ≤ (lower⁻¹ : ℝ) * dist
          (LocalCutoff.CenterProjection.map χ ρ L N ζ u + t)
          (LocalCutoff.CenterProjection.map χ ρ L N ζ u) :=
        (hcenter_inverse_lipschitz ζ).dist_le_mul _ _
      _ = (lower⁻¹ : ℝ) * ‖t‖ := by
        rw [Real.dist_eq, add_sub_cancel_left, Real.norm_eq_abs]
  obtain ⟨Rχ, hRχ_nonneg, hRχ⟩ := hχ_support.isBounded.subset_ball_lt
    0 (0 : ℝ × X)
  obtain ⟨Rmap, hRmap_nonneg, hRmap_eq⟩ :=
    LocalCutoff.CenterProjection.eq_id_of_abs_ge (radius := radius) (slope := slope)
      χ ρ L N hρ hχ_support
  let R : ℝ := max (|ρ| * Rχ) Rmap
  have hR_nonneg : 0 ≤ R := by
    dsimp only [R]
    positivity
  -- The cutoff and the contraction force the fixed graph to vanish outside
  -- the common support buffer; retain this pointwise fact for later branches.
  have hζ_zero_outside (u : ℝ)
      (hu : u ∉ Metric.closedBall (0 : ℝ) R) : ζ u = 0 := by
    have hR_le : R ≤ |u| := by
      have hR_lt : R < |u| := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] using hu
      exact hR_lt.le
    have hRχ_le : |ρ| * Rχ ≤ |u| := (le_max_left _ _).trans hR_le
    have hRmap_le : Rmap ≤ |u| := (le_max_right _ _).trans hR_le
    have hchi_zero : χ (ρ⁻¹ • (u, ζ u)) = 0 := by
      have hscaled_notMem : ρ⁻¹ • (u, ζ u) ∉ tsupport χ := by
        intro hmem
        have hscaled_mem : ρ⁻¹ • (u, ζ u) ∈ Metric.ball (0 : ℝ × X) Rχ := hRχ hmem
        have hscaled_norm : ‖ρ⁻¹ • (u, ζ u)‖ < Rχ := by
          simpa only [Metric.mem_ball, dist_zero_right] using hscaled_mem
        have hρ_abs : 0 < |ρ| := abs_pos.mpr hρ
        have hrestore : ρ • (ρ⁻¹ • (u, ζ u)) = (u, ζ u) := by
          rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
        have hpoint_norm : ‖(u, ζ u)‖ < |ρ| * Rχ := by
          calc
            ‖(u, ζ u)‖ = ‖ρ • (ρ⁻¹ • (u, ζ u))‖ := congrArg norm hrestore.symm
            _ = |ρ| * ‖ρ⁻¹ • (u, ζ u)‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ < |ρ| * Rχ := mul_lt_mul_of_pos_left hscaled_norm hρ_abs
        have hu_lt : |u| < |ρ| * Rχ := by
          calc
            |u| = ‖u‖ := (Real.norm_eq_abs u).symm
            _ ≤ ‖(u, ζ u)‖ := norm_fst_le (u, ζ u)
            _ < |ρ| * Rχ := hpoint_norm
        exact (not_lt_of_ge hRχ_le) hu_lt
      exact image_eq_zero_of_notMem_tsupport hscaled_notMem
    have hinverse :
        LocalCutoff.CenterProjection.inverse χ ρ L N ζ u = u := by
      apply (hcenter_bijective ζ).1
      rw [LocalCutoff.CenterProjection.inverse_def, hRmap_eq ζ u hRmap_le]
      exact Function.rightInverse_invFun (hcenter_bijective ζ).2 u
    have hinvariant := hfixed_apply u
    rw [hinverse, LocalCutoff.centerStableLinearize_apply, hchi_zero,
      zero_smul, add_zero, LocalCutoff.centerStable_apply] at hinvariant
    have hnorm : ‖ζ u‖ ≤ (linearRate : ℝ) * ‖ζ u‖ := by
      calc
        ‖ζ u‖ = ‖(u, L (ζ u)).2‖ := congrArg norm hinvariant
        _ = ‖L (ζ u)‖ := rfl
        _ ≤ ‖L‖ * ‖ζ u‖ := L.le_opNorm _
        _ ≤ (linearRate : ℝ) * ‖ζ u‖ :=
          mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    have hlinearRate_real : (linearRate : ℝ) < 1 := by
      exact_mod_cast h_linearRate
    have hnorm_zero : ‖ζ u‖ = 0 := by
      nlinarith [hlinearRate_real, norm_nonneg (ζ u)]
    exact norm_eq_zero.mp hnorm_zero
  have hζ_support : HasCompactSupport (ζ : ℝ → X) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
    intro u hu
    exact hζ_zero_outside u hu
  -- Reparametrize the fixed-point equation by the forward center coordinate;
  -- bijectivity cancels the inverse appearing in the graph transform.
  have hinvariant_parametrized (u : ℝ) :
      ζ (LocalCutoff.CenterProjection.map χ ρ L N ζ u) =
        (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).2 := by
    calc
      ζ (LocalCutoff.CenterProjection.map χ ρ L N ζ u) =
          (LocalCutoff.centerStableLinearize χ ρ L N
            (LocalCutoff.CenterProjection.inverse χ ρ L N ζ
              (LocalCutoff.CenterProjection.map χ ρ L N ζ u),
              ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ
                (LocalCutoff.CenterProjection.map χ ρ L N ζ u)))).2 :=
        hfixed_apply _
      _ = (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).2 := by
        have hinverse_map :
            LocalCutoff.CenterProjection.inverse χ ρ L N ζ
                (LocalCutoff.CenterProjection.map χ ρ L N ζ u) = u := by
          rw [LocalCutoff.CenterProjection.inverse_def]
          exact Function.leftInverse_invFun (hcenter_bijective ζ).1 u
        rw [hinverse_map]
  -- Compact support and the known `C^(r - 1)` regularity uniformly bound each
  -- canonical Taylor coefficient strictly below the missing top order.
  have hindexOrder_le_predecessor (n : Fin (r + 1))
      (hn : (n : ℕ) < r) :
      ((n : ℕ) : WithTop ENat) ≤ (r : WithTop ENat) - 1 := by
    have hn_enat_lt : ((n : ℕ) : ENat) < (r : ENat) := by
      exact_mod_cast hn
    have hn_enat_le : ((n : ℕ) : ENat) ≤ (r : ENat) - 1 :=
      ENat.le_sub_one_of_lt hn_enat_lt
    simpa using (WithTop.coe_le_coe.mpr hn_enat_le)
  have hcanonicalLower_bounded (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      ∃ C : ℝ≥0, ∀ u,
        ‖(FiniteTaylorJet.ofFunction ℝ r (ζ : ℝ → X) u).coeff n‖ ≤ (C : ℝ) := by
    have hcontinuous :
        Continuous (fun u ↦ iteratedFDeriv ℝ (n : ℕ) (ζ : ℝ → X) u) :=
      hζ_prev.continuous_iteratedFDeriv (hindexOrder_le_predecessor n hn)
    obtain ⟨C, hC⟩ := hcontinuous.bounded_above_of_compact_support
      (hζ_support.iteratedFDeriv (n : ℕ))
    have hC_nonneg : 0 ≤ C :=
      (norm_nonneg (iteratedFDeriv ℝ (n : ℕ) (ζ : ℝ → X) 0)).trans (hC 0)
    let B : ℝ := ‖((n : ℕ).factorial : ℝ)⁻¹‖ * C
    have hB_nonneg : 0 ≤ B :=
      mul_nonneg (norm_nonneg _) hC_nonneg
    refine ⟨Real.toNNReal B, ?_⟩
    intro u
    rw [FiniteTaylorJet.coeff_ofFunction, norm_smul,
      Real.coe_toNNReal B hB_nonneg]
    exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _)
  -- Choose the proved lower bounds degreewise, reserving zero for the top
  -- coefficient that the contraction iteration must construct.
  let lowerCoeffBound : Fin (r + 1) → ℝ≥0 := fun n ↦
    if hn : (n : ℕ) < r then Classical.choose (hcanonicalLower_bounded n hn) else 0
  let initialJetFamily : ℝ → FiniteTaylorJet ℝ ℝ X r := fun u ↦
    { coeff := fun n ↦
        if (n : ℕ) < r then
          (FiniteTaylorJet.ofFunction ℝ r (ζ : ℝ → X) u).coeff n
        else 0 }
  have hinitial_constantCoeff (u : ℝ) :
      (initialJetFamily u).constantCoeff = ζ u := by
    have hzeroCoeff :
        (initialJetFamily u).coeff (0 : Fin (r + 1)) =
          (FiniteTaylorJet.ofFunction ℝ r (ζ : ℝ → X) u).coeff
            (0 : Fin (r + 1)) := by
      have hzero_lt : ((0 : Fin (r + 1)) : ℕ) < r := by
        exact Nat.zero_lt_of_lt hr_pos
      simp only [initialJetFamily]
      rw [if_pos hzero_lt]
    rw [FiniteTaylorJet.constantCoeff_eq_coeff_zero, hzeroCoeff,
      ← FiniteTaylorJet.constantCoeff_eq_coeff_zero,
      FiniteTaylorJet.constantCoeff_ofFunction]
  have hinitial_coeff_le (u : ℝ) (n : Fin (r + 1)) :
      ‖(initialJetFamily u).coeff n‖ ≤ (lowerCoeffBound n : ℝ) := by
    by_cases hn : (n : ℕ) < r
    · simp only [initialJetFamily, hn, if_pos, lowerCoeffBound, dif_pos]
      exact Classical.choose_spec (hcanonicalLower_bounded n hn) u
    · have hcoeff : (initialJetFamily u).coeff n = 0 := by
        simp only [initialJetFamily]
        rw [if_neg hn]
      have hbound : lowerCoeffBound n = 0 := by
        simp only [lowerCoeffBound]
        rw [dif_neg hn]
      rw [hcoeff, hbound, norm_zero, NNReal.coe_zero]
  let J₀ : BoundedGraphJet X radius slope r :=
    BoundedGraphJet.ofJets ζ initialJetFamily lowerCoeffBound hinitial_constantCoeff
      hinitial_coeff_le
  -- The initialized bounded jet has exactly the canonical lower coefficients
  -- and no unproved order-`r` derivative hidden in its top coefficient.
  have hJ₀_lower (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      (J₀.jet u).coeff n =
        (FiniteTaylorJet.ofFunction ℝ r (ζ : ℝ → X) u).coeff n := by
    simp only [J₀, BoundedGraphJet.ofJets, initialJetFamily, hn, if_pos]
  have hJ₀_top (u : ℝ) :
      (J₀.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ = 0 := by
    simp only [J₀, BoundedGraphJet.ofJets, initialJetFamily, lt_self_iff_false, if_false]
  -- Every initialized coefficient is continuous: the lower ones are normalized
  -- predecessor derivatives, while the reserved top coefficient is constantly zero.
  have hJ₀_coeff_continuous (n : Fin (r + 1)) :
      Continuous (fun u ↦ (J₀.jet u).coeff n) := by
    by_cases hn : (n : ℕ) < r
    · have hiterated :
          Continuous (fun u ↦ iteratedFDeriv ℝ (n : ℕ) (ζ : ℝ → X) u) :=
        hζ_prev.continuous_iteratedFDeriv (hindexOrder_le_predecessor n hn)
      have hcoeff : (fun u ↦ (J₀.jet u).coeff n) = fun u ↦
          ((n : ℕ).factorial : ℝ)⁻¹ •
            iteratedFDeriv ℝ (n : ℕ) (ζ : ℝ → X) u := by
        funext u
        rw [hJ₀_lower u n hn, FiniteTaylorJet.coeff_ofFunction]
      rw [hcoeff]
      have hscalar : Continuous (fun _ : ℝ ↦ ((n : ℕ).factorial : ℝ)⁻¹) :=
        continuous_const
      exact hscalar.smul hiterated
    · have hn_eq : (n : ℕ) = r := by omega
      have hfin : n = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext hn_eq
      subst n
      have hcoeff : (fun u ↦ (J₀.jet u).coeff ⟨r, Nat.lt_succ_self r⟩) =
          fun _ ↦ 0 := by
        funext u
        exact hJ₀_top u
      rw [hcoeff]
      exact continuous_const
  let jetMap : BoundedGraphJet X radius slope r → BoundedGraphJet X radius slope r :=
    JetTransform.map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      hrν hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower
      hN_zero hL h_stable_bound h_stable_lipschitz h_radius h_slope
  -- At the base-graph level the differentiated transform is the original
  -- graph transform, hence every bounded jet over the fixed graph stays over it.
  have hjetMap_preserves_fixedGraph (J : BoundedGraphJet X radius slope r)
      (hJ_graph : J.graph = ζ) : (jetMap J).graph = ζ := by
    calc
      (jetMap J).graph =
          GraphTransform.map ν χ ρ L N lower linearRate stableBound stableCenter
            stableFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL
            h_stable_bound h_stable_lipschitz h_radius h_slope J.graph := rfl
      _ = GraphTransform.map ν χ ρ L N lower linearRate stableBound stableCenter
            stableFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL
            h_stable_bound h_stable_lipschitz h_radius h_slope ζ := by rw [hJ_graph]
      _ = ζ := hζ_fixed
  have hjetMap_J₀_graph : (jetMap J₀).graph = ζ :=
    hjetMap_preserves_fixedGraph J₀ rfl
  let q : ℝ≥0 :=
    rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r
  have hq_lt : q < 1 := by
    simpa only [q] using h_bunching
  -- The predecessor recurrence uses one fewer inverse derivative factor than
  -- the top-order contraction.  Record the exact scaling relation once.
  let c : ℝ := (lower⁻¹ : ℝ≥0)
  let p : ℝ :=
    ((rate lower linearRate stableCenter stableFiber centerFiber slope *
      lower⁻¹ ^ (r - 1) : ℝ≥0) : ℝ)
  have hc_pos : 0 < c := by
    dsimp only [c]
    positivity
  have hp_nonneg : 0 ≤ p := by
    dsimp only [p]
    positivity
  have hp_mul_c : p * c = (q : ℝ) := by
    simp only [p, c, q, NNReal.coe_mul, NNReal.coe_pow]
    calc
      ((rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ) *
          ((lower⁻¹ : ℝ≥0) : ℝ) ^ (r - 1) * ((lower⁻¹ : ℝ≥0) : ℝ) =
        ((rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ) *
          (((lower⁻¹ : ℝ≥0) : ℝ) ^ (r - 1) * ((lower⁻¹ : ℝ≥0) : ℝ)) := by ring
      _ = ((rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ) *
          ((lower⁻¹ : ℝ≥0) : ℝ) ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel hr_pos]
  have hq_real_lt : (q : ℝ) < 1 := by
    exact_mod_cast hq_lt
  have hp_lt : p < 1 := by
    by_cases hc_le : c ≤ 1
    · have hpow_le : c ^ (r - 1) ≤ 1 :=
        pow_le_one₀ hc_pos.le hc_le
      have hrate_real_lt :
          ((rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ) <
            1 := by
        exact_mod_cast h_rate
      have hrate_nonneg :
          0 ≤ ((rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ) :=
        NNReal.coe_nonneg _
      calc
        p = ((rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ) *
            c ^ (r - 1) := by
          simp only [p, c, NNReal.coe_mul, NNReal.coe_pow]
        _ ≤ ((rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ) *
            1 :=
          mul_le_mul_of_nonneg_left hpow_le hrate_nonneg
        _ < 1 := by simpa only [mul_one] using hrate_real_lt
    · have hc_gt : 1 < c := lt_of_not_ge hc_le
      nlinarith
  -- The initialized jet supplies the canonical lower coefficients, so the
  -- existing top-coefficient estimate specializes directly to the local map.
  have htop_contract_from_J₀ (J : BoundedGraphJet X radius slope r)
      (hJ_lower : ∀ u (n : Fin (r + 1)), (n : ℕ) < r →
        (J.jet u).coeff n = (J₀.jet u).coeff n) :
      JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩ (jetMap J) (jetMap J₀) ≤
        (q : ℝ) * JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩ J J₀ := by
    simpa only [jetMap, q] using
      JetTransform.topCoeff_contraction r ν χ ρ L N lower linearRate stableBound
        stableCenter stableFiber centerFiber hν hr_pos hrν hχ_smooth hχ_support hρ
        hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL h_linearRate
        h_stable_bound h_stable_lipschitz h_center_fiber h_radius h_slope h_rate
        h_bunching J J₀ hJ_lower
  -- The coefficient distance is nonnegative; this is the order-theoretic
  -- side condition needed when a contraction estimate is iterated.
  have hcoeffDistance_nonneg (J K : BoundedGraphJet X radius slope r) :
      0 ≤ JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K := by
    have hinputBdd : BddAbove (Set.range fun u ↦
        ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
          (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖) := by
      refine ⟨(J.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ) +
        (K.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ), ?_⟩
      rintro _ ⟨u, rfl⟩
      exact (norm_sub_le _ _).trans (add_le_add
        (J.coeff_le u ⟨r, Nat.lt_succ_self r⟩)
        (K.coeff_le u ⟨r, Nat.lt_succ_self r⟩))
    rw [JetTransform.coeffDistance.eq_def]
    exact (norm_nonneg ((J.jet 0).coeff ⟨r, Nat.lt_succ_self r⟩ -
      (K.jet 0).coeff ⟨r, Nat.lt_succ_self r⟩)).trans
        (le_csSup hinputBdd ⟨0, rfl⟩)
  -- The zeroth coefficient is already controlled by the fixed graph equation;
  -- this is the base case of the missing lower-coefficient holonomicity API.
  have hjetMap_zero_coeff (J : BoundedGraphJet X radius slope r)
      (hJ_graph : J.graph = ζ) (u : ℝ) :
      ((jetMap J).jet u).coeff (0 : Fin (r + 1)) =
        (J₀.jet u).coeff (0 : Fin (r + 1)) := by
    apply ContinuousMultilinearMap.ext
    intro z
    have hzero : z = (fun _ ↦ 0) := by
      funext i
      exact Fin.elim0 i
    rw [hzero]
    have hconst : ((jetMap J).jet u).constantCoeff = (J₀.jet u).constantCoeff := by
      rw [(jetMap J).constantCoeff_eq u, hjetMap_preserves_fixedGraph J hJ_graph,
        J₀.constantCoeff_eq u]
      rfl
    simpa only [FiniteTaylorJet.constantCoeff_eq_coeff_zero] using hconst
  -- The coefficient-congruence interface propagates canonical lower data
  -- through the differentiated transform independently of its top coefficient.
  have hjetMap_lower_coeff (J : BoundedGraphJet X radius slope r)
      (hJ_graph : J.graph = ζ)
      (hJ_lower : ∀ u (n : Fin (r + 1)), (n : ℕ) < r →
        (J.jet u).coeff n = (J₀.jet u).coeff n)
      (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      ((jetMap J).jet u).coeff n = ((jetMap J₀).jet u).coeff n := by
    change (JetTransform.differentiatedJet r χ ρ L N J u).coeff n =
      (JetTransform.differentiatedJet r χ ρ L N J₀ u).coeff n
    apply JetTransform.differentiatedJet_coeff_congr_of_lower χ ρ L N J J₀
    · simpa only [J₀, BoundedGraphJet.ofJets] using hJ_graph
    · exact hJ_lower
    · exact hn
  -- The same coefficient bridge is needed for two arbitrary jets in the
  -- Picard iteration; isolating it keeps the iteration independent of the
  -- particular initialization `J₀`.
  have hjetMap_lower_congr (J K : BoundedGraphJet X radius slope r)
      (hJK_graph : J.graph = K.graph)
      (hJK_lower : ∀ u (n : Fin (r + 1)), (n : ℕ) < r →
        (J.jet u).coeff n = (K.jet u).coeff n)
      (u : ℝ) (n : Fin (r + 1)) (hn : (n : ℕ) < r) :
      ((jetMap J).jet u).coeff n = ((jetMap K).jet u).coeff n := by
    change (JetTransform.differentiatedJet r χ ρ L N J u).coeff n =
      (JetTransform.differentiatedJet r χ ρ L N K u).coeff n
    exact JetTransform.differentiatedJet_coeff_congr_of_lower χ ρ L N J K
      hJK_graph hJK_lower n hn u
  -- The inverse-center regularity is available directly from the global inverse
  -- theorem after restricting the given smoothness to the target order.
  have hcenter_inverse_smooth (η : SmallLipschitzGraph X radius slope) :
      ContDiff ℝ r (LocalCutoff.CenterProjection.inverse χ ρ L N η) := by
    rw [LocalCutoff.CenterProjection.inverse_def]
    apply Real.contDiff_invFun_of_pos_le_deriv
    · have hrν_cast : (r : WithTop ENat) ≤ (ν : WithTop ENat) := by
        exact_mod_cast hrν
      exact (h_center_smooth η).of_le hrν_cast
    · exact hr_pos
    · exact h_lower_pos
    · exact h_lower η
  -- The predecessor regularity supplies the Taylor witness used by the
  -- successor update once the missing top derivative has been identified.
  have hζ_prev_taylor := hζ_prev.ftaylorSeries
  -- The predecessor's highest available Taylor coefficient is continuous;
  -- this is the continuity input for the bounded-continuous top-section API.
  have hprev_top_cont :
      Continuous (fun u : ℝ ↦ (ftaylorSeries ℝ (ζ : ℝ → X) u) (r - 1)) := by
    have hpredecessor_order :
        ((r - 1 : ℕ) : WithTop ENat) ≤ (r : WithTop ENat) - 1 := by
      exact_mod_cast le_rfl
    exact hζ_prev_taylor.cont (r - 1) hpredecessor_order
  -- The factorial normalization used by finite jets is cancellable over `ℝ`.
  have hfactorial_ne : ((r.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero r)
  -- The top estimate is independent of the chosen initialization; this is the
  -- pairwise contraction interface needed for a fixed-point construction on top
  -- coefficient sections.
  have htop_contract_pair (J K : BoundedGraphJet X radius slope r)
      (hJK_lower : ∀ u (n : Fin (r + 1)), (n : ℕ) < r →
        (J.jet u).coeff n = (K.jet u).coeff n) :
      JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩ (jetMap J) (jetMap K) ≤
        (q : ℝ) * JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K := by
    simpa only [jetMap, q] using
      JetTransform.topCoeff_contraction r ν χ ρ L N lower linearRate stableBound
        stableCenter stableFiber centerFiber hν hr_pos hrν hχ_smooth hχ_support hρ
        hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL h_linearRate
        h_stable_bound h_stable_lipschitz h_center_fiber h_radius h_slope h_rate
        h_bunching J K hJK_lower
  -- Updating only the top coefficient preserves all lower coefficients, so the
  -- jet contraction specializes to the top-section interface constructed above.
  have htopUpdated_contract
      (a b : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) :
      JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩
          (jetMap (JetTransform.topUpdatedGraphJet r hr_strict J₀ a))
          (jetMap (JetTransform.topUpdatedGraphJet r hr_strict J₀ b)) ≤
        (q : ℝ) * JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩
          (JetTransform.topUpdatedGraphJet r hr_strict J₀ a)
          (JetTransform.topUpdatedGraphJet r hr_strict J₀ b) := by
    apply htop_contract_pair
    intro u n hn
    calc
      ((JetTransform.topUpdatedGraphJet r hr_strict J₀ a).jet u).coeff n =
          (J₀.jet u).coeff n :=
        JetTransform.topUpdatedGraphJet_coeff_of_lt r hr_strict J₀ a u n hn
      _ = ((JetTransform.topUpdatedGraphJet r hr_strict J₀ b).jet u).coeff n :=
        (JetTransform.topUpdatedGraphJet_coeff_of_lt r hr_strict J₀ b u n hn).symm
  -- Consequently the raw transformed top coefficient is already a pointwise
  -- contraction; only its continuity remains before the BCF fixed-point theorem applies.
  have htopSectionValue_contract
      (a b : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) (u : ℝ) :
      dist (JetTransform.topSectionValue hr_strict J₀ jetMap a u)
          (JetTransform.topSectionValue hr_strict J₀ jetMap b u) ≤
        (q : ℝ) * dist a b := by
    simpa only [JetTransform.topSectionValue] using
      JetTransform.topUpdatedGraphJet_topCoeff_dist_le_of_coeffDistance
        hr_strict J₀ a b jetMap q (htopUpdated_contract a b) u
  -- Once coefficientwise continuity is supplied, the contraction theorem gives
  -- both the bounded section and its pointwise fixed-section equation.
  have hfixed_topSection_equation
      (hcontinuous : ∀ a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X),
        Continuous (JetTransform.topSectionValue hr_strict J₀ jetMap a)) :
      ∃ a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X),
        (JetTransform.topSectionOperator hr_strict J₀ jetMap hcontinuous a = a) ∧
          ∀ u, JetTransform.topSectionValue hr_strict J₀ jetMap a u = a u := by
    obtain ⟨a, ha, _⟩ := JetTransform.existsUnique_fixedPoint_topSectionOperator
      hr_strict J₀ jetMap q hq_lt hcontinuous htopUpdated_contract
    refine ⟨a, ha, ?_⟩
    intro u
    calc
      JetTransform.topSectionValue hr_strict J₀ jetMap a u =
          (JetTransform.topSectionOperator hr_strict J₀ jetMap hcontinuous a) u :=
        (JetTransform.topSectionOperator_apply hr_strict J₀ jetMap hcontinuous a u).symm
      _ = a u := congrArg (fun f : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X) ↦ f u) ha
  -- Expose continuity of the transformed top coefficient without unfolding the
  -- bounded-function fixed-point construction.
  have htopSectionValue_continuous
      (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X)) :
      Continuous (JetTransform.topSectionValue hr_strict J₀ jetMap a) := by
    have hcontinuous_of_apply_one
        {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
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
    have hcomp_coeff_continuous
        {F G : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
        [NormedAddCommGroup G] [NormedSpace ℝ G]
        (P : ℝ → FiniteTaylorJet ℝ ℝ F r)
        (Q : ℝ → FiniteTaylorJet ℝ F G r)
        (hP : ∀ n : Fin (r + 1), Continuous (fun u ↦ (P u).coeff n))
        (hQ : ∀ n : Fin (r + 1), Continuous (fun u ↦ (Q u).coeff n))
        (n : Fin (r + 1)) :
        Continuous (fun u ↦ (FiniteTaylorJet.comp (Q u) (P u)).coeff n) := by
      apply hcontinuous_of_apply_one
      simp only [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp,
        _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
      apply continuous_finsetSum
      intro c _
      have hlengthOrder : c.length ≤ r :=
        c.length_le.trans (Nat.le_of_lt_succ n.isLt)
      have houter : Continuous (fun u ↦ (Q u).toFormalMultilinearSeries c.length) := by
        have houter_eq : (fun u ↦ (Q u).toFormalMultilinearSeries c.length) =
            fun u ↦ (Q u).coeff ⟨c.length, Nat.lt_succ_iff.mpr hlengthOrder⟩ := by
          funext u
          exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le (Q u) hlengthOrder
        rw [houter_eq]
        exact hQ _
      have hinner (i : Fin c.length) :
          Continuous (fun u ↦
            (P u).toFormalMultilinearSeries (c.blocksFun i)) := by
        have hblockOrder : c.blocksFun i ≤ r :=
          (c.blocksFun_le i).trans (Nat.le_of_lt_succ n.isLt)
        have hinner_eq :
            (fun u ↦ (P u).toFormalMultilinearSeries (c.blocksFun i)) =
              fun u ↦ (P u).coeff
                ⟨c.blocksFun i, Nat.lt_succ_iff.mpr hblockOrder⟩ := by
          funext u
          exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le (P u) hblockOrder
        rw [hinner_eq]
        exact hP _
      have hinner_apply (i : Fin c.length) : Continuous (fun u ↦
          (P u).toFormalMultilinearSeries (c.blocksFun i)
            (fun _ ↦ (1 : ℝ))) :=
        (hinner i).eval continuous_const
      exact houter.eval (continuous_pi hinner_apply)
    have hcomp_real_coeff_continuous
        (P : ℝ → FiniteTaylorJet ℝ ℝ ℝ r)
        (Q : ℝ → FiniteTaylorJet ℝ ℝ X r)
        (hP : ∀ n : Fin (r + 1), Continuous (fun u ↦ (P u).coeff n))
        (hQ : ∀ n : Fin (r + 1), Continuous (fun u ↦ (Q u).coeff n))
        (n : Fin (r + 1)) :
        Continuous (fun u ↦ (FiniteTaylorJet.comp (Q u) (P u)).coeff n) := by
      apply hcontinuous_of_apply_one
      simp only [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp,
        _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
      apply continuous_finsetSum
      intro c _
      have hlengthOrder : c.length ≤ r :=
        c.length_le.trans (Nat.le_of_lt_succ n.isLt)
      have houter : Continuous (fun u ↦ (Q u).toFormalMultilinearSeries c.length) := by
        have houter_eq : (fun u ↦ (Q u).toFormalMultilinearSeries c.length) =
            fun u ↦ (Q u).coeff ⟨c.length, Nat.lt_succ_iff.mpr hlengthOrder⟩ := by
          funext u
          exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le (Q u) hlengthOrder
        rw [houter_eq]
        exact hQ _
      have hinner (i : Fin c.length) :
          Continuous (fun u ↦
            (P u).toFormalMultilinearSeries (c.blocksFun i)) := by
        have hblockOrder : c.blocksFun i ≤ r :=
          (c.blocksFun_le i).trans (Nat.le_of_lt_succ n.isLt)
        have hinner_eq :
            (fun u ↦ (P u).toFormalMultilinearSeries (c.blocksFun i)) =
              fun u ↦ (P u).coeff
                ⟨c.blocksFun i, Nat.lt_succ_iff.mpr hblockOrder⟩ := by
          funext u
          exact FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le (P u) hblockOrder
        rw [hinner_eq]
        exact hP _
      have hinner_apply (i : Fin c.length) : Continuous (fun u ↦
          (P u).toFormalMultilinearSeries (c.blocksFun i)
            (fun _ ↦ (1 : ℝ))) :=
        (hinner i).eval continuous_const
      exact houter.eval (continuous_pi hinner_apply)
    have hofFunction_coeff_continuous
        {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup F] [NormedSpace ℝ F]
        (f : E → F) (hf : ContDiff ℝ r f) (n : Fin (r + 1)) :
        Continuous (fun x ↦ (FiniteTaylorJet.ofFunction ℝ r f x).coeff n) := by
      have hcoeff_formula :
          (fun x ↦ (FiniteTaylorJet.ofFunction ℝ r f x).coeff n) =
          fun x ↦ ((n : ℕ).factorial : ℝ)⁻¹ •
            iteratedFDeriv ℝ (n : ℕ) f x := by
        funext x
        exact FiniteTaylorJet.coeff_ofFunction r f x n
      rw [hcoeff_formula]
      have hscalar : Continuous (fun _ : E ↦ ((n : ℕ).factorial : ℝ)⁻¹) :=
        continuous_const
      have hn_order :
          ((n : ℕ) : WithTop ENat) ≤ (r : WithTop ENat) := by
        exact_mod_cast Nat.le_of_lt_succ n.isLt
      exact hscalar.smul (hf.continuous_iteratedFDeriv hn_order)
    have hconstantCoeff_continuous
        {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (P : ℝ → FiniteTaylorJet ℝ ℝ F r)
        (hP : Continuous (fun u ↦ (P u).coeff (0 : Fin (r + 1)))) :
        Continuous (fun u ↦ (P u).constantCoeff) := by
      have hconstant_eq : (fun u ↦ (P u).constantCoeff) = fun u ↦
          (P u).coeff (0 : Fin (r + 1)) (fun _ ↦ 0) := by
        funext u
        exact FiniteTaylorJet.constantCoeff_eq_coeff_zero (P u)
      rw [hconstant_eq]
      exact hP.eval continuous_const
    have hcutoff_smooth : ContDiff ℝ ν (fun p : ℝ × X ↦ χ (ρ⁻¹ • p)) :=
      hχ_smooth.comp (contDiff_const_smul ρ⁻¹)
    have hremainder_eq : LocalCutoff.remainder χ ρ N =
        (fun p : ℝ × X ↦ χ (ρ⁻¹ • p)) • N := by
      funext p
      exact LocalCutoff.remainder_apply χ ρ N p
    have hlinearize_eq : LocalCutoff.centerStableLinearize χ ρ L N =
        LocalCutoff.centerStable L + LocalCutoff.remainder χ ρ N := by
      funext p
      rw [Pi.add_apply, LocalCutoff.centerStableLinearize_apply,
        LocalCutoff.remainder_apply]
    have hlinearize_smooth :
        ContDiff ℝ r (LocalCutoff.centerStableLinearize χ ρ L N) := by
      have hsmooth : ContDiff ℝ ν (LocalCutoff.centerStableLinearize χ ρ L N) := by
        rw [hlinearize_eq, hremainder_eq]
        exact (LocalCutoff.centerStable L).contDiff.add (hcutoff_smooth.smul hN_smooth)
      have hr_order : (r : WithTop ENat) ≤ (ν : WithTop ENat) := by
        exact_mod_cast hrν
      exact hsmooth.of_le hr_order
    let J : BoundedGraphJet X radius slope r :=
      JetTransform.topUpdatedGraphJet r hr_strict J₀ a
    have hJ_coeff (n : Fin (r + 1)) :
        Continuous (fun u ↦ (J.jet u).coeff n) := by
      exact JetTransform.continuous_topUpdatedGraphJet_coeff r hr_strict J₀
        hJ₀_coeff_continuous a n
    have hparam_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (JetTransform.graphParametrizationJet r J u).coeff n) := by
      apply hcontinuous_of_apply_one
      simp only [JetTransform.graphParametrizationJet, FiniteTaylorJet.coeff_prod,
        ContinuousMultilinearMap.prod_apply]
      have hid_coeff : Continuous (fun u : ℝ ↦
          (FiniteTaylorJet.ofFunction ℝ r id u).coeff n) := by
        have hid_coeff_formula :
            (fun u : ℝ ↦ (FiniteTaylorJet.ofFunction ℝ r id u).coeff n) =
            fun u ↦ ((n : ℕ).factorial : ℝ)⁻¹ •
              iteratedFDeriv ℝ (n : ℕ) id u := by
          funext u
          exact FiniteTaylorJet.coeff_ofFunction r id u n
        rw [hid_coeff_formula]
        have hscalar : Continuous (fun _ : ℝ ↦ ((n : ℕ).factorial : ℝ)⁻¹) :=
          continuous_const
        have hn_order :
            ((n : ℕ) : WithTop ENat) ≤ (r : WithTop ENat) := by
          exact_mod_cast Nat.le_of_lt_succ n.isLt
        exact hscalar.smul ((contDiff_id : ContDiff ℝ r (id : ℝ → ℝ))
          |>.continuous_iteratedFDeriv hn_order)
      have hid_apply : Continuous (fun u : ℝ ↦
          (FiniteTaylorJet.ofFunction ℝ r id u).coeff n (fun _ ↦ 1)) :=
        hid_coeff.eval continuous_const
      have hJ_apply : Continuous (fun u : ℝ ↦
          (J.jet u).coeff n (fun _ ↦ 1)) :=
        (hJ_coeff n).eval continuous_const
      exact hid_apply.prodMk hJ_apply
    have hparam_constant : Continuous (fun u ↦
        (JetTransform.graphParametrizationJet r J u).constantCoeff) :=
      hconstantCoeff_continuous _ (hparam_coeff (0 : Fin (r + 1)))
    have himage_outer_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (FiniteTaylorJet.ofFunction ℝ r (LocalCutoff.centerStableLinearize χ ρ L N)
          (JetTransform.graphParametrizationJet r J u).constantCoeff).coeff n) :=
      (hofFunction_coeff_continuous _ hlinearize_smooth n).comp hparam_constant
    have himage_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (JetTransform.imageJet r χ ρ L N J u).coeff n) := by
      simpa only [JetTransform.imageJet, FiniteTaylorJet.postcomp_def] using
        hcomp_coeff_continuous (JetTransform.graphParametrizationJet r J)
          (fun u ↦ FiniteTaylorJet.ofFunction ℝ r
            (LocalCutoff.centerStableLinearize χ ρ L N)
              (JetTransform.graphParametrizationJet r J u).constantCoeff)
          hparam_coeff himage_outer_coeff n
    have himage_constant : Continuous (fun u ↦
        (JetTransform.imageJet r χ ρ L N J u).constantCoeff) :=
      hconstantCoeff_continuous _ (himage_coeff (0 : Fin (r + 1)))
    have hstable_outer_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (FiniteTaylorJet.ofFunction ℝ r Prod.snd
          (JetTransform.imageJet r χ ρ L N J u).constantCoeff).coeff n) :=
      (hofFunction_coeff_continuous Prod.snd contDiff_snd n).comp himage_constant
    have hstable_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (JetTransform.stableJet r χ ρ L N J u).coeff n) := by
      simpa only [JetTransform.stableJet, FiniteTaylorJet.postcomp_def] using
        hcomp_coeff_continuous (JetTransform.imageJet r χ ρ L N J)
          (fun u ↦ FiniteTaylorJet.ofFunction ℝ r Prod.snd
            (JetTransform.imageJet r χ ρ L N J u).constantCoeff)
          himage_coeff hstable_outer_coeff n
    have hinverse_smooth := hcenter_inverse_smooth J.graph
    have hinverse_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (FiniteTaylorJet.ofFunction ℝ r
          (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) u).coeff n) := by
      have hinverse_coeff_formula :
          (fun u ↦ (FiniteTaylorJet.ofFunction ℝ r
          (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) u).coeff n) =
          fun u ↦ ((n : ℕ).factorial : ℝ)⁻¹ • iteratedFDeriv ℝ (n : ℕ)
            (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) u := by
        funext u
        exact FiniteTaylorJet.coeff_ofFunction r _ u n
      rw [hinverse_coeff_formula]
      have hscalar : Continuous (fun _ : ℝ ↦ ((n : ℕ).factorial : ℝ)⁻¹) :=
        continuous_const
      have hn_order :
          ((n : ℕ) : WithTop ENat) ≤ (r : WithTop ENat) := by
        exact_mod_cast Nat.le_of_lt_succ n.isLt
      exact hscalar.smul
        (hinverse_smooth.continuous_iteratedFDeriv hn_order)
    have hstable_inverse_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (JetTransform.stableJet r χ ρ L N J
          (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u)).coeff n) :=
      (hstable_coeff n).comp hinverse_smooth.continuous
    have hdifferentiated_coeff (n : Fin (r + 1)) : Continuous (fun u ↦
        (JetTransform.differentiatedJet r χ ρ L N J u).coeff n) := by
      simpa only [JetTransform.differentiatedJet] using
        hcomp_real_coeff_continuous
          (fun u ↦ FiniteTaylorJet.ofFunction ℝ r
            (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph) u)
          (fun u ↦ JetTransform.stableJet r χ ρ L N J
            (LocalCutoff.CenterProjection.inverse χ ρ L N J.graph u))
          hinverse_coeff hstable_inverse_coeff n
    unfold JetTransform.topSectionValue jetMap JetTransform.map
    dsimp only [BoundedGraphJet.ofJets]
    simpa only [J] using hdifferentiated_coeff ⟨r, Nat.lt_succ_self r⟩

  -- Route correction: the monolithic endpoint proof exhausted elaboration
  -- while constructing dependent all-ones secants, so the next pass must use
  -- typed theorem-local transport and support lemmas.
  -- TODO: restore the finite-order endpoint proof from a theorem-local
  -- support module once the projected endpoint certificate is available.
  have hpredecessor_contDiff_one :
      ContDiff ℝ 1 (iteratedDeriv (r - 1) (ζ : ℝ → X)) := by
    by_cases hr_high : 2 ≤ r
    · have hm : 0 < r - 1 := by omega
      let inverseCenter : ℝ → ℝ :=
        LocalCutoff.CenterProjection.inverse χ ρ L N ζ
      let stableOutput : ℝ × X → X := fun point ↦
        (LocalCutoff.centerStableLinearize χ ρ L N point).2
      let predecessorValue : ℝ → X :=
        iteratedDeriv (r - 1) (ζ : ℝ → X)
      let coefficient : ℝ → X →L[ℝ] X :=
        nestedPrincipalOperator (r - 1) hm inverseCenter
          (ζ : ℝ → X) stableOutput
      let forcing : ℝ → X :=
        nestedEndpointForcing (r - 1) inverseCenter
          (ζ : ℝ → X) stableOutput
      have hcutoff_smooth : ContDiff ℝ ν
          (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) :=
        hχ_smooth.comp (contDiff_const_smul ρ⁻¹)
      have hremainder_eq : LocalCutoff.remainder χ ρ N =
          (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) • N := by
        funext point
        exact LocalCutoff.remainder_apply χ ρ N point
      have hremainder_smooth : ContDiff ℝ ν
          (LocalCutoff.remainder χ ρ N) := by
        rw [hremainder_eq]
        exact hcutoff_smooth.smul hN_smooth
      have hlinearize_eq : LocalCutoff.centerStableLinearize χ ρ L N =
          LocalCutoff.centerStable L + LocalCutoff.remainder χ ρ N := by
        funext point
        rw [Pi.add_apply, LocalCutoff.centerStableLinearize_apply,
          LocalCutoff.remainder_apply]
      have hr_le_nu_order :
          (r : WithTop ENat) ≤ (ν : WithTop ENat) := by
        exact_mod_cast hrν
      have hone_le_nu_nat : 1 ≤ ν := by omega
      have hone_le_nu_order :
          (1 : WithTop ENat) ≤ (ν : WithTop ENat) := by
        exact_mod_cast hone_le_nu_nat
      have hlinearize_smooth : ContDiff ℝ r
          (LocalCutoff.centerStableLinearize χ ρ L N) := by
        have hlinearize_smooth_nu : ContDiff ℝ ν
            (LocalCutoff.centerStableLinearize χ ρ L N) := by
          rw [hlinearize_eq]
          exact (LocalCutoff.centerStable L).contDiff.add hremainder_smooth
        exact hlinearize_smooth_nu.of_le hr_le_nu_order
      have hstableOutput_smooth : ContDiff ℝ r stableOutput := by
        exact hlinearize_smooth.snd
      have horder : r - 1 + 1 = r := Nat.sub_add_cancel hr_pos
      have horder_prev : (r : WithTop ENat) - 1 =
          ((r - 1 : ℕ) : WithTop ENat) := by
        calc
          (r : WithTop ENat) - 1 =
              (((r : ENat) - (1 : ENat) : ENat) : WithTop ENat) :=
            (WithTop.coe_sub (a := (r : ENat)) (b := (1 : ENat))).symm
          _ = (((r - 1 : ℕ) : ENat) : WithTop ENat) :=
            congrArg (fun n : ENat ↦ (n : WithTop ENat))
              (ENat.coe_sub r 1).symm
      have horder_top :
          (r : WithTop ENat) - 1 + 1 = (r : WithTop ENat) := by
        rw [horder_prev]
        exact_mod_cast horder
      have hpredecessor_order_le :
          ((r - 1 : ℕ) : WithTop ENat) ≤
            (r : WithTop ENat) - 1 + 1 := by
        rw [horder_top]
        exact_mod_cast Nat.sub_le r 1
      have hone_le_r_nat : 1 ≤ r := by omega
      have hone_le_r_order :
          (1 : WithTop ENat) ≤ (r : WithTop ENat) := by
        exact_mod_cast hone_le_r_nat
      have hinverse_order : ContDiff ℝ (r - 1 + 1) inverseCenter := by
        simpa only [horder_top, inverseCenter] using hcenter_inverse_smooth ζ
      have hinverse_one : ContDiff ℝ 1 inverseCenter := by
        apply hinverse_order.of_le
        simpa only [horder_top] using hone_le_r_order
      have hstable_order : ContDiff ℝ (r - 1 + 1) stableOutput := by
        simpa only [horder_top] using hstableOutput_smooth
      have hstableOutput_one : ContDiff ℝ 1 stableOutput :=
        hstableOutput_smooth.of_le hone_le_r_order
      have hcoefficient_smooth : ContDiff ℝ 1 coefficient := by
        exact contDiffOne_nestedPrincipalOperator hm inverseCenter
          (ζ : ℝ → X) stableOutput hinverse_order hζ_prev hstable_order
      have hforcing_smooth : ContDiff ℝ 1 forcing := by
        exact contDiffOne_nestedEndpointForcing hm inverseCenter
          (ζ : ℝ → X) stableOutput hinverse_order hζ_prev hstable_order
      have hendpoint (y : ℝ) :
          nestedEndpointJet (r - 1) inverseCenter (ζ : ℝ → X)
              stableOutput y =
            FiniteTaylorJet.ofFunction ℝ (r - 1) (ζ : ℝ → X) y := by
        exact nestedEndpointJet_eq_of_fixedEquation inverseCenter
          (ζ : ℝ → X) stableOutput
          (hinverse_order.of_le hpredecessor_order_le) hζ_prev
          (hstable_order.of_le hpredecessor_order_le) hfixed_apply y
      have hpredecessor_equation (y : ℝ) :
          predecessorValue y =
            coefficient y (predecessorValue (inverseCenter y)) + forcing y := by
        exact iteratedDeriv_eq_nestedPrincipal_add_truncatedEndpoint hm
          inverseCenter (ζ : ℝ → X) stableOutput y (hendpoint y)
      have hpredecessor_continuous : Continuous predecessorValue := by
        dsimp only [predecessorValue]
        exact hζ_prev.continuous_iteratedDeriv (r - 1) le_rfl
      have hpredecessor_support : HasCompactSupport predecessorValue := by
        exact iteratedDeriv_hasCompactSupport hζ_support (r - 1)
      let Pfactor : ℝ≥0 :=
        rate lower linearRate stableCenter stableFiber centerFiber slope *
          lower⁻¹ ^ (r - 1)
      let Cfactor : ℝ≥0 := lower⁻¹
      have hPfactor_coe : (Pfactor : ℝ) = p := by
        rfl
      have hCfactor_coe : (Cfactor : ℝ) = c := by
        rfl
      have hPfactor_lt : Pfactor < 1 := by
        exact_mod_cast hp_lt
      have hPfactor_mul_Cfactor : Pfactor * Cfactor = q := by
        apply NNReal.eq
        change (Pfactor : ℝ) * (Cfactor : ℝ) = (q : ℝ)
        rw [hPfactor_coe, hCfactor_coe]
        exact hp_mul_c
      have hPfactorCfactor_lt : Pfactor * Cfactor < 1 := by
        rw [hPfactor_mul_Cfactor]
        exact hq_lt
      have hinverse_deriv_norm (y : ℝ) :
          ‖deriv inverseCenter y‖ ≤ (Cfactor : ℝ) := by
        simpa only [Cfactor] using
          (norm_deriv_le_of_lipschitz (hcenter_inverse_lipschitz ζ)
            (x₀ := y))
      have hstableFiber_fderiv (y : ℝ) :
          fderiv ℝ
              (fun z : X ↦ stableOutput (inverseCenter y, z))
              (ζ (inverseCenter y)) =
            (fderiv ℝ stableOutput
              (inverseCenter y, ζ (inverseCenter y))).comp
                (ContinuousLinearMap.inr ℝ ℝ X) := by
        have houter : HasFDerivAt stableOutput
            (fderiv ℝ stableOutput
              (inverseCenter y, ζ (inverseCenter y)))
            (inverseCenter y, ζ (inverseCenter y)) :=
          (hstableOutput_one.differentiable one_ne_zero
            (inverseCenter y, ζ (inverseCenter y))).hasFDerivAt
        have hcomp := houter.comp (ζ (inverseCenter y))
          (hasFDerivAt_prodMk_right (inverseCenter y)
            (ζ (inverseCenter y)))
        have hslice : (fun z : X ↦ stableOutput (inverseCenter y, z)) =
            stableOutput ∘ Prod.mk (inverseCenter y) := by
          rfl
        rw [hslice]
        exact hcomp.fderiv
      have hfirstInverseCoefficient_norm (y : ℝ) :
          ‖(FiniteTaylorJet.ofFunction ℝ (r - 1) inverseCenter y).coeff
              ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ (1 : ℝ))‖ ≤
            (lower⁻¹ : ℝ) := by
        calc
          _ ≤ ‖(FiniteTaylorJet.ofFunction ℝ (r - 1) inverseCenter y).coeff
                ⟨1, Nat.succ_lt_succ hm⟩‖ := by
            simpa only [norm_one, Finset.prod_const_one, mul_one] using
              (ContinuousMultilinearMap.le_opNorm
                ((FiniteTaylorJet.ofFunction ℝ (r - 1) inverseCenter y).coeff
                  ⟨1, Nat.succ_lt_succ hm⟩)
                (fun _ : Fin 1 ↦ (1 : ℝ)))
          _ ≤ (lower⁻¹ : ℝ) := by
            simp only [inverseCenter, FiniteTaylorJet.coeff_ofFunction,
              Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
              norm_iteratedFDeriv_eq_norm_iteratedDeriv,
              LocalCutoff.CenterProjection.inverse_def]
            exact Real.norm_iteratedDeriv_one_invFun_le
              ((h_center_smooth ζ).of_le hone_le_nu_order)
              h_lower_pos (h_lower ζ) y
      have hstableFiberDerivative_norm (y : ℝ) :
          ‖(fderiv ℝ stableOutput
              (inverseCenter y, ζ (inverseCenter y))).comp
                (ContinuousLinearMap.inr ℝ ℝ X)‖ ≤
            ((linearRate + stableFiber : ℝ≥0) : ℝ) := by
        rw [← hstableFiber_fderiv]
        exact norm_fderiv_le_of_lipschitz ℝ
          (JetTransform.stableOutput_lipschitzWith (inverseCenter y)
            χ ρ L N linearRate stableCenter stableFiber hL h_stable_lipschitz)
      have hstable_le_rate :
          ((linearRate + stableFiber : ℝ≥0) : ℝ) ≤
            (rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) := by
        have htail_nonneg : (0 : ℝ≥0) ≤
            (stableCenter + (linearRate + stableFiber) * slope) *
              lower⁻¹ * centerFiber := by
          positivity
        have hstable_le_rate_nnreal : linearRate + stableFiber ≤
            rate lower linearRate stableCenter stableFiber centerFiber slope := by
          rw [rate_def]
          exact le_add_of_nonneg_right htail_nonneg
        exact_mod_cast hstable_le_rate_nnreal
      have hcoefficient_norm (y : ℝ) :
          ‖coefficient y‖ ≤ (Pfactor : ℝ) := by
        have hinverse_nonneg : 0 ≤ (lower⁻¹ : ℝ) := by positivity
        calc
          ‖coefficient y‖ =
              ‖(FiniteTaylorJet.ofFunction ℝ (r - 1) inverseCenter y).coeff
                  ⟨1, Nat.succ_lt_succ hm⟩
                  (fun _ : Fin 1 ↦ (1 : ℝ))‖ ^ (r - 1) *
                ‖(fderiv ℝ stableOutput
                  (inverseCenter y, ζ (inverseCenter y))).comp
                    (ContinuousLinearMap.inr ℝ ℝ X)‖ := by
            simp only [coefficient, nestedPrincipalOperator, norm_smul,
              norm_pow, Real.norm_eq_abs]
          _ ≤ (lower⁻¹ : ℝ) ^ (r - 1) *
                ((linearRate + stableFiber : ℝ≥0) : ℝ) := by
            gcongr
            · exact hfirstInverseCoefficient_norm y
            · exact hstableFiberDerivative_norm y
          _ ≤ (lower⁻¹ : ℝ) ^ (r - 1) *
                (rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) :=
            mul_le_mul_of_nonneg_left hstable_le_rate
              (pow_nonneg hinverse_nonneg _)
          _ = (Pfactor : ℝ) := by
            simp only [Pfactor, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
            ring
      have hinverse_eventuallyEq_id (y : ℝ)
          (hy : y ∉ Metric.closedBall (0 : ℝ) R) :
          inverseCenter =ᶠ[𝓝 y] (id : ℝ → ℝ) := by
        have hopen : IsOpen (Metric.closedBall (0 : ℝ) R)ᶜ :=
          Metric.isClosed_closedBall.isOpen_compl
        filter_upwards [hopen.mem_nhds hy] with z hz
        have hz_notMem : z ∉ Metric.closedBall (0 : ℝ) R := by
          simpa only [Set.mem_compl_iff] using hz
        have hzR : R < |z| := by
          simpa only [Metric.mem_closedBall, dist_zero_right,
            Real.norm_eq_abs, not_le] using hz_notMem
        have hzRmap : Rmap ≤ |z| :=
          (le_max_right _ _).trans hzR.le
        have hmap : LocalCutoff.CenterProjection.map χ ρ L N ζ z = z :=
          hRmap_eq ζ z hzRmap
        apply (hcenter_bijective ζ).1
        dsimp only [inverseCenter]
        rw [LocalCutoff.CenterProjection.inverse_def]
        simpa only [id] using
          (Function.rightInverse_invFun (hcenter_bijective ζ).2 z).trans
            hmap.symm
      have hscaledCutoff_tsupport :
          tsupport (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) =
            ρ • tsupport χ := by
        rw [tsupport, support_comp_inv_smul₀ hρ, tsupport]
        exact closure_smul₀' hρ _
      have hstableOutput_exterior (y : ℝ)
          (hy : y ∉ Metric.closedBall (0 : ℝ) R) :
          stableOutput =ᶠ[𝓝 (y, (0 : X))]
            fun point : ℝ × X ↦ L point.2 := by
        have hy_norm : R < |y| := by
          simpa only [Metric.mem_closedBall, dist_zero_right,
            Real.norm_eq_abs, not_le] using hy
        have hscaled_notMem : (y, (0 : X)) ∉
            tsupport (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) := by
          rw [hscaledCutoff_tsupport]
          intro hmem
          obtain ⟨point, hpoint, hpoint_eq⟩ := Set.mem_smul_set.mp hmem
          have hpoint_ball : point ∈ Metric.ball (0 : ℝ × X) Rχ :=
            hRχ hpoint
          have hpoint_norm : ‖point‖ < Rχ := by
            simpa only [Metric.mem_ball, dist_zero_right] using hpoint_ball
          have hy_lt : |y| < |ρ| * Rχ := by
            calc
              |y| = ‖(y, (0 : X))‖ := by
                simp only [Prod.norm_def, norm_zero, max_eq_left,
                  Real.norm_eq_abs, abs_nonneg]
              _ = ‖ρ • point‖ := congrArg norm hpoint_eq.symm
              _ = |ρ| * ‖point‖ := by
                rw [norm_smul, Real.norm_eq_abs]
              _ < |ρ| * Rχ :=
                mul_lt_mul_of_pos_left hpoint_norm (abs_pos.mpr hρ)
          exact (not_lt_of_ge ((le_max_left _ _).trans hy_norm.le)) hy_lt
        have hremainder_notMem : (y, (0 : X)) ∉
            tsupport (LocalCutoff.remainder χ ρ N) := by
          intro hmem
          apply hscaled_notMem
          rw [hremainder_eq] at hmem
          exact (tsupport_smul_subset_left
            (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) N) hmem
        have hopen : IsOpen
            (tsupport (LocalCutoff.remainder χ ρ N))ᶜ :=
          (isClosed_tsupport _).isOpen_compl
        have hremainder_zero : LocalCutoff.remainder χ ρ N =ᶠ[
            𝓝 (y, (0 : X))] fun _ : ℝ × X ↦ (0 : ℝ × X) := by
          filter_upwards [hopen.mem_nhds hremainder_notMem] with point hpoint
          exact image_eq_zero_of_notMem_tsupport hpoint
        filter_upwards [hremainder_zero] with point hpoint
        dsimp only [stableOutput]
        have hlinearize_apply :
            LocalCutoff.centerStableLinearize χ ρ L N point =
              LocalCutoff.centerStable L point +
                LocalCutoff.remainder χ ρ N point := by
          rw [LocalCutoff.centerStableLinearize_apply,
            LocalCutoff.remainder_apply]
        rw [hlinearize_apply]
        rw [hpoint, add_zero, LocalCutoff.centerStable_apply]
      have hcoefficient_exterior (y : ℝ)
          (hy : y ∉ Metric.closedBall (0 : ℝ) R) : coefficient y = L := by
        have hinverse_local := hinverse_eventuallyEq_id y hy
        have hinverse_eq : inverseCenter y = y :=
          hinverse_local.self_of_nhds
        have hζ_zero : ζ y = 0 := hζ_zero_outside y hy
        have hfirst :
            (FiniteTaylorJet.ofFunction ℝ (r - 1) inverseCenter y).coeff
                ⟨1, Nat.succ_lt_succ hm⟩
                (fun _ : Fin 1 ↦ (1 : ℝ)) = 1 := by
          rw [FiniteTaylorJet.coeff_ofFunction_apply]
          simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
            iteratedFDeriv_one_apply]
          rw [hinverse_local.fderiv_eq]
          simp only [fderiv_id, ContinuousLinearMap.id_apply]
        have hstableFiber :
            (fderiv ℝ stableOutput (y, (0 : X))).comp
                (ContinuousLinearMap.inr ℝ ℝ X) = L := by
          rw [(hstableOutput_exterior y hy).fderiv_eq]
          let fiberLinear : ℝ × X →L[ℝ] X :=
            L.comp (ContinuousLinearMap.snd ℝ ℝ X)
          change (fderiv ℝ fiberLinear (y, (0 : X))).comp
              (ContinuousLinearMap.inr ℝ ℝ X) = L
          rw [ContinuousLinearMap.fderiv]
          ext z
          rfl
        simp only [coefficient, nestedPrincipalOperator, hinverse_eq, hζ_zero,
          hfirst, one_pow, one_smul, hstableFiber]
      have hcoefficient_sub_support : HasCompactSupport
          (fun y ↦ coefficient y - L) := by
        apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
        intro y hy
        rw [hcoefficient_exterior y hy, sub_self]
      have hcoefficient_deriv_support :
          HasCompactSupport (deriv coefficient) := by
        have hsupport := hcoefficient_sub_support.deriv
        change HasCompactSupport
          (deriv (coefficient - fun _ : ℝ ↦ L)) at hsupport
        have hderiv_eq :
            deriv (coefficient - fun _ : ℝ ↦ L) = deriv coefficient := by
          have hsubtracted_eq :
              coefficient - (fun _ : ℝ ↦ L) =
                fun y ↦ coefficient y - L := by
            rfl
          rw [hsubtracted_eq]
          funext y
          have hsub :=
            ((hcoefficient_smooth.differentiable one_ne_zero y).hasDerivAt).sub_const L
          exact hsub.deriv
        rw [hderiv_eq] at hsupport
        exact hsupport
      have hpredecessor_exterior (y : ℝ)
          (hy : y ∉ Metric.closedBall (0 : ℝ) R) :
          predecessorValue y = 0 := by
        have hopen : IsOpen (Metric.closedBall (0 : ℝ) R)ᶜ :=
          Metric.isClosed_closedBall.isOpen_compl
        have hζ_local : (ζ : ℝ → X) =ᶠ[𝓝 y]
            fun _ : ℝ ↦ (0 : X) := by
          filter_upwards [hopen.mem_nhds hy] with z hz
          exact hζ_zero_outside z hz
        have hderiv := hζ_local.iteratedDeriv_eq (r - 1)
        simpa only [predecessorValue, iteratedDeriv_fun_const_zero]
          using hderiv
      have hforcing_exterior (y : ℝ)
          (hy : y ∉ Metric.closedBall (0 : ℝ) R) : forcing y = 0 := by
        have hinverse_eq : inverseCenter y = y :=
          (hinverse_eventuallyEq_id y hy).self_of_nhds
        have hequation := hpredecessor_equation y
        rw [hpredecessor_exterior y hy, hinverse_eq,
          hpredecessor_exterior y hy, hcoefficient_exterior y hy,
          map_zero, zero_add] at hequation
        exact hequation.symm
      have hforcing_support : HasCompactSupport forcing := by
        apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
        exact hforcing_exterior
      have hforcing_deriv_support : HasCompactSupport (deriv forcing) :=
        hforcing_support.deriv
      obtain ⟨MA, hMA⟩ :=
        exists_nnreal_norm_bound_of_continuous_compactSupport
          (deriv coefficient) (hcoefficient_smooth.continuous_deriv le_rfl)
          hcoefficient_deriv_support
      obtain ⟨BF, hBF⟩ :=
        exists_nnreal_norm_bound_of_continuous_compactSupport
          forcing hforcing_smooth.continuous hforcing_support
      obtain ⟨BDF, hBDF⟩ :=
        exists_nnreal_norm_bound_of_continuous_compactSupport
          (deriv forcing) (hforcing_smooth.continuous_deriv le_rfl)
          hforcing_deriv_support
      obtain ⟨BW, hBW⟩ :=
        exists_nnreal_norm_bound_of_continuous_compactSupport
          predecessorValue hpredecessor_continuous hpredecessor_support
      exact contDiffOne_of_affinePicard_fixedPoint inverseCenter coefficient
        forcing predecessorValue Pfactor Cfactor MA BF BDF BW
        hinverse_one
        hcoefficient_smooth hforcing_smooth hpredecessor_continuous
        hpredecessor_equation hPfactor_lt hPfactorCfactor_lt
        hcoefficient_norm hinverse_deriv_norm hMA hBF hBDF hBW
    have hr_one : r = 1 := by omega
    have hpredecessor_order_le_nu :
        ((r - 1 : ℕ) : WithTop ENat) ≤ (ν : WithTop ENat) := by
      have hpredecessor_order_nat : r - 1 ≤ ν :=
        (Nat.sub_le r 1).trans hrν
      exact_mod_cast hpredecessor_order_nat
    subst r
    let r : ℕ := 1
    -- The contraction API supplies a bounded fixed top section.  Its repeated-
    -- one evaluation is the only possible derivative field for the predecessor.
    obtain ⟨a, ha_fixed, ha_equation⟩ :=
      hfixed_topSection_equation htopSectionValue_continuous
    let oneTop : Fin r → ℝ := fun _ ↦ 1
    let predecessorValue : ℝ → X :=
      iteratedDeriv (r - 1) (ζ : ℝ → X)
    let derivativeValue : ℝ → X := fun u ↦
      (r.factorial : ℝ) • a u oneTop
    -- Evaluation of a bounded-continuous section at a fixed vector preserves
    -- continuity, as does multiplication by the factorial scalar.
    have hderivativeValue_continuous : Continuous derivativeValue := by
      dsimp only [derivativeValue]
      exact continuous_const.smul (a.continuous.eval continuous_const)
    -- Reparametrize the fixed top-section equation at a forward center.  This
    -- is the common candidate-compatibility interface for the order-one,
    -- order-two, and higher affine-cocycle branches below.
    have ha_equation_parametrized (u : ℝ) :
        a (LocalCutoff.CenterProjection.map χ ρ L N ζ u) =
            (JetTransform.differentiatedJet r χ ρ L N
              (JetTransform.topUpdatedGraphJet r hr_strict J₀ a)
              (LocalCutoff.CenterProjection.map χ ρ L N ζ u)).coeff
              ⟨r, Nat.lt_succ_self r⟩ := by
      have h := ha_equation
        (LocalCutoff.CenterProjection.map χ ρ L N ζ u)
      have hmap := JetTransform.map_spec r ν χ ρ L N lower linearRate
        stableBound stableCenter stableFiber hν hrν hχ_smooth hχ_support hρ
        hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL
        h_stable_bound h_stable_lipschitz h_radius h_slope
        (JetTransform.topUpdatedGraphJet r hr_strict J₀ a)
      rw [JetTransform.topSectionValue, hmap.2] at h
      exact h.symm
    -- Reduce the derivative goal to one explicit bounded-section secant
    -- certificate.  Its formula records the all-ones endpoint and its limit.
    -- Route correction: the available projection lemmas stop at a decomposition
    -- of the endpoint into principal and non-principal branches; they do not
    -- identify the principal branch with the transported predecessor defect.
    have hpredecessor_secant_certificate :
        ∃ sections : ℝ → BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X),
          Tendsto sections (𝓝 0) (𝓝 a) ∧
            ∀ u : ℝ,
              (fun t : ℝ => t⁻¹ •
                (predecessorValue (u + t) - predecessorValue u)) =ᶠ[
                  nhdsWithin 0 ({0}ᶜ : Set ℝ)]
                (fun t => (r.factorial : ℝ) •
                  (sections t u) oneTop) := by
      have hpredecessorIndex_bound : r - 1 < r + 1 := by
        omega
      let predecessorIndex : Fin (r + 1) :=
        ⟨r - 1, hpredecessorIndex_bound⟩
      have hpredecessorIndex_lt : (predecessorIndex : ℕ) < r := by
        dsimp only [predecessorIndex]
        omega
      obtain ⟨predecessorBound, hpredecessorBound⟩ :=
        hcanonicalLower_bounded predecessorIndex hpredecessorIndex_lt
      have hpredecessor_continuous : Continuous predecessorValue := by
        dsimp only [predecessorValue]
        apply hζ_prev.continuous_iteratedDeriv
        exact_mod_cast le_rfl
      let predecessorNormBound : ℝ :=
        ((r - 1).factorial : ℝ) * (predecessorBound : ℝ)
      have hpredecessor_norm_le (u : ℝ) :
          ‖predecessorValue u‖ ≤ predecessorNormBound := by
        have hcoeffValue :
            ((FiniteTaylorJet.ofFunction ℝ r (ζ : ℝ → X) u).coeff
                predecessorIndex) (fun _ ↦ (1 : ℝ)) =
              ((r - 1).factorial : ℝ)⁻¹ • predecessorValue u := by
          rw [FiniteTaylorJet.coeff_ofFunction_apply]
          rfl
        have hcoeffNorm :
            ‖((FiniteTaylorJet.ofFunction ℝ r (ζ : ℝ → X) u).coeff
                predecessorIndex) (fun _ ↦ (1 : ℝ))‖ ≤
              (predecessorBound : ℝ) := by
          calc
            _ ≤ ‖(FiniteTaylorJet.ofFunction ℝ r
                    (ζ : ℝ → X) u).coeff predecessorIndex‖ *
                  ∏ _i : Fin (r - 1), ‖(1 : ℝ)‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
            _ = ‖(FiniteTaylorJet.ofFunction ℝ r
                    (ζ : ℝ → X) u).coeff predecessorIndex‖ := by
              simp only [norm_one, Finset.prod_const_one, mul_one]
            _ ≤ (predecessorBound : ℝ) := hpredecessorBound u
        have hfactorial_pos : 0 < ((r - 1).factorial : ℝ) := by
          positivity
        calc
          ‖predecessorValue u‖ =
              ‖((r - 1).factorial : ℝ) •
                ((FiniteTaylorJet.ofFunction ℝ r
                    (ζ : ℝ → X) u).coeff predecessorIndex)
                  (fun _ ↦ (1 : ℝ))‖ := by
            rw [hcoeffValue, smul_smul,
              mul_inv_cancel₀ hfactorial_pos.ne', one_smul]
          _ = ((r - 1).factorial : ℝ) *
                ‖((FiniteTaylorJet.ofFunction ℝ r
                    (ζ : ℝ → X) u).coeff predecessorIndex)
                  (fun _ ↦ (1 : ℝ))‖ := by
            rw [norm_smul, Real.norm_of_nonneg hfactorial_pos.le]
          _ ≤ ((r - 1).factorial : ℝ) * (predecessorBound : ℝ) :=
            mul_le_mul_of_nonneg_left hcoeffNorm hfactorial_pos.le
          _ = predecessorNormBound := rfl
      obtain ⟨sections, hsections_zero, hsections_apply_one,
          hsections_distance, hsecant⟩ :=
        exists_factorialNormalizedSecantSections predecessorValue
          hpredecessor_continuous predecessorNormBound
          hpredecessor_norm_le a
      -- The generic interface above settles boundedness, continuity in the
      -- base point, factorial normalization, and the exact punctured secant
      -- identity.  Expose the source-specific endpoint in output coordinates,
      -- then pass its affine recurrence through the generic radius envelope.
      have hsections_tendsto : Tendsto sections (𝓝 0) (𝓝 a) := by
        let inverseCenter : ℝ → ℝ :=
          LocalCutoff.CenterProjection.inverse χ ρ L N ζ
        have hinverseCenter_forward (u : ℝ) :
            inverseCenter
                (LocalCutoff.CenterProjection.map χ ρ L N ζ u) = u := by
          dsimp only [inverseCenter]
          rw [LocalCutoff.CenterProjection.inverse_def]
          exact Function.leftInverse_invFun (hcenter_bijective ζ).1 u
        have hforwardCenter_inverse (y : ℝ) :
            LocalCutoff.CenterProjection.map χ ρ L N ζ (inverseCenter y) = y := by
          dsimp only [inverseCenter]
          rw [LocalCutoff.CenterProjection.inverse_def]
          exact Function.rightInverse_invFun (hcenter_bijective ζ).2 y
        have htransported_endpoint (u s : ℝ) :
            LocalCutoff.CenterProjection.map χ ρ L N ζ
                (inverseCenter u +
                  (inverseCenter (u + s) - inverseCenter u)) = u + s := by
          have hargument :
              inverseCenter u +
                  (inverseCenter (u + s) - inverseCenter u) =
                inverseCenter (u + s) := by
            ring
          calc
            LocalCutoff.CenterProjection.map χ ρ L N ζ
                (inverseCenter u +
                  (inverseCenter (u + s) - inverseCenter u)) =
                LocalCutoff.CenterProjection.map χ ρ L N ζ
                  (inverseCenter (u + s)) := by
                    exact congrArg (LocalCutoff.CenterProjection.map χ ρ L N ζ)
                      hargument
            _ = u + s := hforwardCenter_inverse (u + s)
        have htransported_increment_ne (u s : ℝ) (hs : s ≠ 0) :
            inverseCenter (u + s) - inverseCenter u ≠ 0 := by
          intro hzero
          have hinverse_eq : inverseCenter (u + s) = inverseCenter u :=
            sub_eq_zero.mp hzero
          have houtput_eq := congrArg
            (LocalCutoff.CenterProjection.map χ ρ L N ζ) hinverse_eq
          rw [hforwardCenter_inverse, hforwardCenter_inverse] at houtput_eq
          apply hs
          linarith
        have hcenter_endpoint_difference (u s : ℝ) :
            s =
              (LocalCutoff.centerStableLinearize χ ρ L N
                  (inverseCenter (u + s), ζ (inverseCenter (u + s)))).1 -
                (LocalCutoff.centerStableLinearize χ ρ L N
                  (inverseCenter u, ζ (inverseCenter u))).1 := by
          calc
            s = (u + s) - u := by ring
            _ = LocalCutoff.CenterProjection.map χ ρ L N ζ
                    (inverseCenter (u + s)) -
                  LocalCutoff.CenterProjection.map χ ρ L N ζ
                    (inverseCenter u) := by
              rw [hforwardCenter_inverse, hforwardCenter_inverse]
            _ = _ := by
              rw [LocalCutoff.CenterProjection.map_apply,
                LocalCutoff.CenterProjection.map_apply]
        have horderOne_stable_endpoint_difference
            (hr_one : r = 1) (u s : ℝ) :
            predecessorValue (u + s) - predecessorValue u =
              (LocalCutoff.centerStableLinearize χ ρ L N
                  (inverseCenter (u + s), ζ (inverseCenter (u + s)))).2 -
                (LocalCutoff.centerStableLinearize χ ρ L N
                  (inverseCenter u, ζ (inverseCenter u))).2 := by
          subst r
          calc
            predecessorValue (u + s) - predecessorValue u =
                ζ (u + s) - ζ u := by
                  simp [predecessorValue]
            _ = (LocalCutoff.centerStableLinearize χ ρ L N
                  (inverseCenter (u + s), ζ (inverseCenter (u + s)))).2 -
                (LocalCutoff.centerStableLinearize χ ρ L N
                  (inverseCenter u, ζ (inverseCenter u))).2 := by
                  rw [hfixed_apply (u + s), hfixed_apply u]
        have hJ₀_graph : J₀.graph = ζ := by
          rfl
        have htopUpdated_graph :
            (JetTransform.topUpdatedGraphJet r hr_strict J₀ a).graph = ζ := by
          rw [JetTransform.topUpdatedGraphJet_graph, hJ₀_graph]
        have hinverse_at_map (u : ℝ) :
            LocalCutoff.CenterProjection.inverse χ ρ L N ζ
                (LocalCutoff.CenterProjection.map χ ρ L N ζ u) = u := by
          rw [LocalCutoff.CenterProjection.inverse_def]
          exact Function.leftInverse_invFun (hcenter_bijective ζ).1 u
        let fixedEndpoint : ℝ → (ℝ [×r]→L[ℝ] X) := fun y ↦
          (FiniteTaylorJet.comp
            (JetTransform.stableJet r χ ρ L N
              (JetTransform.topUpdatedGraphJet r hr_strict J₀ a)
              (inverseCenter y))
            (FiniteTaylorJet.ofFunction ℝ r inverseCenter y)).coeff
              ⟨r, Nat.lt_succ_self r⟩
        have hfixedEndpoint_eq_section_forward (u : ℝ) :
            a (LocalCutoff.CenterProjection.map χ ρ L N ζ u) =
              fixedEndpoint
                (LocalCutoff.CenterProjection.map χ ρ L N ζ u) := by
          simpa only [fixedEndpoint, JetTransform.differentiatedJet,
            htopUpdated_graph, hinverseCenter_forward, hinverse_at_map] using
            ha_equation_parametrized u
        have hderivativeValue_forward (u : ℝ) :
            derivativeValue
                (LocalCutoff.CenterProjection.map χ ρ L N ζ u) =
              (r.factorial : ℝ) •
                (fixedEndpoint
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ u)) oneTop := by
          dsimp only [derivativeValue]
          rw [hfixedEndpoint_eq_section_forward]
        let rawTopDefect (u h : ℝ) : X :=
          predecessorValue (u + h) - predecessorValue u - h • derivativeValue u
        have hrawTopDefect_zero (u : ℝ) : rawTopDefect u 0 = 0 := by
          simp only [rawTopDefect, add_zero, sub_self, zero_smul]
        let inverseEndpointJet : ℝ → FiniteTaylorJet ℝ ℝ ℝ r := fun u ↦
          FiniteTaylorJet.ofFunction ℝ r inverseCenter u
        let principalOperator : ℝ → X →L[ℝ] X := fun u ↦
          (((inverseEndpointJet u).coeff
                ⟨1, Nat.succ_lt_succ hr_strict⟩
                (fun _ : Fin 1 ↦ (1 : ℝ))) ^ (r - 1)) •
            fderiv ℝ
              (fun x : X ↦
                (LocalCutoff.centerStableLinearize χ ρ L N
                  (inverseCenter u, x)).2)
              (ζ (inverseCenter u))
        let filteredEndpoint : ℝ → (ℝ [×r]→L[ℝ] X) := fun u ↦
          (FiniteTaylorJet.comp
            (truncateTopCoeff
              (JetTransform.stableJet r χ ρ L N J₀ (inverseCenter u)))
            (inverseEndpointJet u)).coeff ⟨r, Nat.lt_succ_self r⟩
        have hν_one_nat : 1 ≤ ν := by
          omega
        have hν_one : (1 : WithTop ENat) ≤ (ν : WithTop ENat) := by
          exact_mod_cast hν_one_nat
        have hinverseEndpointCoeff_norm_le (u : ℝ) :
            ‖(inverseEndpointJet u).coeff
                ⟨1, Nat.succ_lt_succ hr_strict⟩
                (fun _ : Fin 1 ↦ (1 : ℝ))‖ ≤ (lower⁻¹ : ℝ) := by
          calc
            _ ≤ ‖(inverseEndpointJet u).coeff
                  ⟨1, Nat.succ_lt_succ hr_strict⟩‖ := by
              simpa only [norm_one, Finset.prod_const_one, mul_one] using
                (ContinuousMultilinearMap.le_opNorm
                  ((inverseEndpointJet u).coeff
                    ⟨1, Nat.succ_lt_succ hr_strict⟩)
                  (fun _ : Fin 1 ↦ (1 : ℝ)))
            _ ≤ (lower⁻¹ : ℝ) := by
              simp only [inverseEndpointJet, inverseCenter,
                FiniteTaylorJet.coeff_ofFunction, Nat.factorial_one,
                Nat.cast_one, inv_one, one_smul,
                norm_iteratedFDeriv_eq_norm_iteratedDeriv,
                LocalCutoff.CenterProjection.inverse_def]
              exact Real.norm_iteratedDeriv_one_invFun_le
                ((h_center_smooth ζ).of_le hν_one) h_lower_pos
                  (h_lower ζ) u
        have hstableFiberDerivative_norm_le (u : ℝ) :
            ‖fderiv ℝ
                (fun x : X ↦
                  (LocalCutoff.centerStableLinearize χ ρ L N
                    (inverseCenter u, x)).2)
                (ζ (inverseCenter u))‖ ≤
              ((linearRate + stableFiber : ℝ≥0) : ℝ) := by
          exact norm_fderiv_le_of_lipschitz ℝ
            (JetTransform.stableOutput_lipschitzWith (inverseCenter u)
              χ ρ L N linearRate stableCenter stableFiber hL h_stable_lipschitz)
        have hstable_le_rate :
            ((linearRate + stableFiber : ℝ≥0) : ℝ) ≤
              (rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) := by
          have hrate_tail_nonneg :
              0 ≤ (stableCenter + (linearRate + stableFiber) * slope) *
                lower⁻¹ * centerFiber := by
            positivity
          have hstable_le_rate_nnreal :
              linearRate + stableFiber ≤
                rate lower linearRate stableCenter stableFiber centerFiber slope := by
            rw [rate_def]
            exact le_add_of_nonneg_right hrate_tail_nonneg
          exact_mod_cast hstable_le_rate_nnreal
        have hprincipalOperator_norm_le (u : ℝ) :
            ‖principalOperator u‖ ≤ p := by
          have hlowerInverse_nonneg : 0 ≤ (lower⁻¹ : ℝ) := by
            positivity
          have hlowerInversePow_nonneg :
              0 ≤ (lower⁻¹ : ℝ) ^ (r - 1) :=
            pow_nonneg hlowerInverse_nonneg _
          calc
            ‖principalOperator u‖ =
                ‖(inverseEndpointJet u).coeff
                    ⟨1, Nat.succ_lt_succ hr_strict⟩
                    (fun _ : Fin 1 ↦ (1 : ℝ))‖ ^ (r - 1) *
                  ‖fderiv ℝ
                    (fun x : X ↦
                      (LocalCutoff.centerStableLinearize χ ρ L N
                        (inverseCenter u, x)).2)
                    (ζ (inverseCenter u))‖ := by
              simp only [principalOperator, norm_smul, norm_pow,
                Real.norm_eq_abs]
            _ ≤ (lower⁻¹ : ℝ) ^ (r - 1) *
                  ((linearRate + stableFiber : ℝ≥0) : ℝ) := by
              gcongr
              exact hinverseEndpointCoeff_norm_le u
              exact hstableFiberDerivative_norm_le u
            _ ≤ (lower⁻¹ : ℝ) ^ (r - 1) *
                  (rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) :=
              mul_le_mul_of_nonneg_left hstable_le_rate hlowerInversePow_nonneg
            _ = p := by
              simp only [p, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
              ring
        -- The filtered non-ones endpoint is continuous.  This proof is kept at
        -- coefficient level, so the convergence argument never unfolds the
        -- full differentiated-jet construction.
        have hlinearize_smooth_fixed :
            ContDiff ℝ r (LocalCutoff.centerStableLinearize χ ρ L N) := by
          have hcutoff_smooth : ContDiff ℝ ν
              (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) :=
            hχ_smooth.comp (contDiff_const_smul ρ⁻¹)
          have hremainder_eq :
              LocalCutoff.remainder χ ρ N =
                (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) • N := by
            funext point
            exact LocalCutoff.remainder_apply χ ρ N point
          have hremainder_smooth : ContDiff ℝ ν
              (LocalCutoff.remainder χ ρ N) := by
            rw [hremainder_eq]
            exact hcutoff_smooth.smul hN_smooth
          have hlinearize_eq :
              LocalCutoff.centerStableLinearize χ ρ L N =
                LocalCutoff.centerStable L + LocalCutoff.remainder χ ρ N := by
            funext point
            rw [Pi.add_apply, LocalCutoff.centerStableLinearize_apply,
              LocalCutoff.remainder_apply]
          have hlinearize_smooth_nu : ContDiff ℝ ν
              (LocalCutoff.centerStableLinearize χ ρ L N) := by
            rw [hlinearize_eq]
            exact (LocalCutoff.centerStable L).contDiff.add hremainder_smooth
          have hr_le_nu : (r : WithTop ENat) ≤ (ν : WithTop ENat) := by
            exact_mod_cast hrν
          exact hlinearize_smooth_nu.of_le hr_le_nu
        have hparam_coeff_fixed (n : Fin (r + 1)) : Continuous (fun u ↦
            (JetTransform.graphParametrizationJet r J₀ u).coeff n) := by
          simpa only [JetTransform.graphParametrizationJet] using
            FiniteTaylorJet.continuous_prod_coeff
              (fun u : ℝ ↦ FiniteTaylorJet.ofFunction ℝ r id u)
              (fun u : ℝ ↦ J₀.jet u)
              (fun k ↦ FiniteTaylorJet.continuous_ofFunction_coeff r id
                contDiff_id k)
              hJ₀_coeff_continuous n
        have hparam_constant_fixed : Continuous (fun u ↦
            (JetTransform.graphParametrizationJet r J₀ u).constantCoeff) :=
          FiniteTaylorJet.continuous_constantCoeff_of_coeff_zero _
            (hparam_coeff_fixed (0 : Fin (r + 1)))
        have himage_outer_coeff_fixed (n : Fin (r + 1)) : Continuous (fun u ↦
            (FiniteTaylorJet.ofFunction ℝ r
              (LocalCutoff.centerStableLinearize χ ρ L N)
              (JetTransform.graphParametrizationJet r J₀ u).constantCoeff).coeff n) :=
          (FiniteTaylorJet.continuous_ofFunction_coeff r
            (LocalCutoff.centerStableLinearize χ ρ L N)
            hlinearize_smooth_fixed n).comp hparam_constant_fixed
        have himage_coeff_fixed (n : Fin (r + 1)) : Continuous (fun u ↦
            (JetTransform.imageJet r χ ρ L N J₀ u).coeff n) := by
          simpa only [JetTransform.imageJet, FiniteTaylorJet.postcomp_def] using
            FiniteTaylorJet.continuous_comp_coeff
              (JetTransform.graphParametrizationJet r J₀)
              (fun u ↦ FiniteTaylorJet.ofFunction ℝ r
                (LocalCutoff.centerStableLinearize χ ρ L N)
                (JetTransform.graphParametrizationJet r J₀ u).constantCoeff)
              hparam_coeff_fixed himage_outer_coeff_fixed n
        have himage_constant_fixed : Continuous (fun u ↦
            (JetTransform.imageJet r χ ρ L N J₀ u).constantCoeff) :=
          FiniteTaylorJet.continuous_constantCoeff_of_coeff_zero _
            (himage_coeff_fixed (0 : Fin (r + 1)))
        have hstable_outer_coeff_fixed (n : Fin (r + 1)) : Continuous (fun u ↦
            (FiniteTaylorJet.ofFunction ℝ r Prod.snd
              (JetTransform.imageJet r χ ρ L N J₀ u).constantCoeff).coeff n) :=
          (FiniteTaylorJet.continuous_ofFunction_coeff r Prod.snd contDiff_snd n).comp
            himage_constant_fixed
        have hstable_coeff_fixed (n : Fin (r + 1)) : Continuous (fun u ↦
            (JetTransform.stableJet r χ ρ L N J₀ u).coeff n) := by
          simpa only [JetTransform.stableJet, FiniteTaylorJet.postcomp_def] using
            FiniteTaylorJet.continuous_comp_coeff
              (JetTransform.imageJet r χ ρ L N J₀)
              (fun u ↦ FiniteTaylorJet.ofFunction ℝ r Prod.snd
                (JetTransform.imageJet r χ ρ L N J₀ u).constantCoeff)
              himage_coeff_fixed hstable_outer_coeff_fixed n
        have hstable_inverse_coeff_fixed (n : Fin (r + 1)) : Continuous (fun u ↦
            (JetTransform.stableJet r χ ρ L N J₀ (inverseCenter u)).coeff n) :=
          (hstable_coeff_fixed n).comp (hcenter_inverse_smooth ζ).continuous
        have hinverseEndpointJet_coeff_continuous (n : Fin (r + 1)) :
            Continuous (fun u ↦ (inverseEndpointJet u).coeff n) := by
          dsimp only [inverseEndpointJet, inverseCenter]
          exact FiniteTaylorJet.continuous_ofFunction_coeff r
            (LocalCutoff.CenterProjection.inverse χ ρ L N ζ)
            (hcenter_inverse_smooth ζ) n
        have hfilteredEndpoint_continuous : Continuous filteredEndpoint := by
          dsimp only [filteredEndpoint]
          apply continuousScalarCompositionCoeff
          · intro n
            exact hinverseEndpointJet_coeff_continuous n
          · intro n
            by_cases hn : (n : ℕ) < r
            · have hfun : (fun u ↦
                  (truncateTopCoeff
                    (JetTransform.stableJet r χ ρ L N J₀
                      (inverseCenter u))).coeff n) = (fun u ↦
                (JetTransform.stableJet r χ ρ L N J₀
                  (inverseCenter u)).coeff n) := by
                funext u
                rw [truncateTopCoeff,
                  FiniteTaylorJet.replaceTopCoeff_coeff_of_lt _ 0 n hn]
              rw [hfun]
              exact hstable_inverse_coeff_fixed n
            · have htop : n = ⟨r, Nat.lt_succ_self r⟩ := by
                apply Fin.ext
                exact Nat.le_antisymm (Nat.le_of_lt_succ n.isLt)
                  (Nat.le_of_not_gt hn)
              subst n
              simp only [truncateTopCoeff,
                FiniteTaylorJet.replaceTopCoeff_coeff_top]
              exact continuous_const
        have hfilteredEndpoint_uniform (ε : ℝ) (hε : 0 < ε) :
            ∃ δ > 0, ∀ u ∈ Metric.closedBall (0 : ℝ) (R + 1), ∀ h : ℝ,
              ‖h‖ < δ → ‖filteredEndpoint (u + h) - filteredEndpoint u‖ < ε := by
          let K : Set ℝ := Metric.closedBall (0 : ℝ) (R + 2)
          have hKuniform : UniformContinuousOn filteredEndpoint K :=
            (isCompact_closedBall (0 : ℝ) (R + 2)).uniformContinuousOn_of_continuous
              hfilteredEndpoint_continuous.continuousOn
          obtain ⟨δ₀, hδ₀, hδ₀_spec⟩ :=
            (Metric.uniformContinuousOn_iff.mp hKuniform) ε hε
          have hone_pos : (0 : ℝ) < 1 := by
            norm_num
          refine ⟨min δ₀ 1, lt_min hδ₀ hone_pos, ?_⟩
          intro u hu h hh
          have hu_norm : ‖u‖ ≤ R + 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using hu
          have hu_mem : u ∈ K := by
            dsimp only [K]
            rw [Metric.mem_closedBall, dist_zero_right]
            linarith [norm_nonneg u]
          have huv_norm : ‖u + h‖ < R + 2 := by
            calc
              ‖u + h‖ ≤ ‖u‖ + ‖h‖ := norm_add_le _ _
              _ < (R + 1) + 1 := add_lt_add_of_le_of_lt hu_norm
                (lt_of_lt_of_le hh (min_le_right _ _))
              _ = R + 2 := by ring
          have huv_mem : u + h ∈ K := by
            dsimp only [K]
            rw [Metric.mem_closedBall, dist_zero_right]
            exact huv_norm.le
          have hdist : dist u (u + h) < δ₀ := by
            calc
              dist u (u + h) = ‖h‖ := by
                rw [dist_eq_norm, norm_sub_rev, add_sub_cancel_left]
              _ < min δ₀ 1 := hh
              _ ≤ δ₀ := min_le_left _ _
          have hbound := hδ₀_spec u hu_mem (u + h) huv_mem hdist
          rw [dist_eq_norm, norm_sub_rev] at hbound
          exact hbound
        have hinverse_eventuallyEq_id (z : ℝ)
            (hz : z ∉ Metric.closedBall (0 : ℝ) R) :
            inverseCenter =ᶠ[𝓝 z] (id : ℝ → ℝ) := by
          have hopen : IsOpen (Metric.closedBall (0 : ℝ) R)ᶜ :=
            (Metric.isClosed_closedBall :
              IsClosed (Metric.closedBall (0 : ℝ) R)).isOpen_compl
          filter_upwards [hopen.mem_nhds hz] with y hy
          have hyR : R < |y| := by
            apply lt_of_not_ge
            intro hyR
            apply hy
            simpa only [Metric.mem_closedBall, dist_zero_right,
              Real.norm_eq_abs] using hyR
          have hyRmap : Rmap ≤ |y| :=
            (le_max_right _ _).trans hyR.le
          have hmap : LocalCutoff.CenterProjection.map χ ρ L N ζ y = y :=
            hRmap_eq ζ y hyRmap
          apply (hcenter_bijective ζ).1
          dsimp only [inverseCenter]
          rw [LocalCutoff.CenterProjection.inverse_def]
          simpa only [id] using
            (Function.rightInverse_invFun (hcenter_bijective ζ).2 y).trans hmap.symm
        have hinverseEndpointJet_eq_id (z : ℝ)
            (hz : z ∉ Metric.closedBall (0 : ℝ) R) :
            inverseEndpointJet z =
              FiniteTaylorJet.ofFunction ℝ r (id : ℝ → ℝ) z := by
          dsimp only [inverseEndpointJet]
          exact FiniteTaylorJet.ofFunction_eq_of_eventuallyEq
            (contDiffAt_id.congr_of_eventuallyEq
              (hinverse_eventuallyEq_id z hz))
            contDiffAt_id (hinverse_eventuallyEq_id z hz)
        have hfilteredEndpoint_zero_exterior (z : ℝ)
            (hz : z ∉ Metric.closedBall (0 : ℝ) R) :
            filteredEndpoint z = 0 := by
          dsimp only [filteredEndpoint]
          rw [hinverseEndpointJet_eq_id z hz]
          exact topCoeff_truncateTopCoeff_comp_identity_zero r
            (JetTransform.stableJet r χ ρ L N J₀ (inverseCenter z)) z
        have hfilteredEndpoint_forcing_compact (η : ℝ) (hη : 0 < η) :
            ∃ δ > 0, ∀ u ∈ Metric.closedBall (0 : ℝ) (R + 1), ∀ s : ℝ,
              ‖s‖ < δ →
                ‖(r.factorial : ℝ) •
                  (s • ((filteredEndpoint u - filteredEndpoint (u + s)) oneTop))‖ ≤
                  (η / 2) * ‖s‖ := by
          have hfactorial_pos : 0 < (r.factorial : ℝ) := by
            positivity
          have hmodulus_pos : 0 < η / (2 * (r.factorial : ℝ)) := by
            positivity
          obtain ⟨δ, hδ, hmodulus⟩ :=
            hfilteredEndpoint_uniform
              (η / (2 * (r.factorial : ℝ))) hmodulus_pos
          refine ⟨δ, hδ, ?_⟩
          intro u hu s hs
          have hfiltered := hmodulus u hu s hs
          have heval :
              ‖((filteredEndpoint u - filteredEndpoint (u + s)) oneTop)‖ <
                η / (2 * (r.factorial : ℝ)) := by
            calc
              ‖((filteredEndpoint u - filteredEndpoint (u + s)) oneTop)‖ ≤
                  ‖filteredEndpoint u - filteredEndpoint (u + s)‖ *
                    ∏ i : Fin r, ‖oneTop i‖ :=
                ContinuousMultilinearMap.le_opNorm _ _
              _ = ‖filteredEndpoint u - filteredEndpoint (u + s)‖ := by
                simp only [oneTop, norm_one, Finset.prod_const_one, mul_one]
              _ < η / (2 * (r.factorial : ℝ)) := by
                rw [norm_sub_rev]
                exact hfiltered
          calc
            ‖(r.factorial : ℝ) •
                (s • ((filteredEndpoint u - filteredEndpoint (u + s)) oneTop))‖ =
                (r.factorial : ℝ) * ‖s‖ *
                  ‖((filteredEndpoint u - filteredEndpoint (u + s)) oneTop)‖ := by
              rw [norm_smul, norm_smul,
                Real.norm_of_nonneg hfactorial_pos.le, mul_assoc]
            _ ≤ (r.factorial : ℝ) * ‖s‖ *
                  (η / (2 * (r.factorial : ℝ))) :=
              mul_le_mul_of_nonneg_left heval.le
                (mul_nonneg hfactorial_pos.le (norm_nonneg s))
            _ = (η / 2) * ‖s‖ := by
              field_simp [hfactorial_pos.ne']
        have hfilteredEndpoint_residual_uniform (η : ℝ) (hη : 0 < η) :
            ∃ δ > 0, ∀ u s : ℝ, ‖s‖ < δ →
              ‖(r.factorial : ℝ) •
                  (s • ((filteredEndpoint u - filteredEndpoint (u + s)) oneTop))‖ ≤
                η * ‖s‖ := by
          obtain ⟨δcompact, hδcompact, hcompact⟩ :=
            hfilteredEndpoint_forcing_compact η hη
          have hone_pos : (0 : ℝ) < 1 := by
            norm_num
          refine ⟨min 1 δcompact, lt_min hone_pos hδcompact, ?_⟩
          intro u s hsδ
          by_cases hu : u ∈ Metric.closedBall (0 : ℝ) (R + 1)
          · have hscompact : ‖s‖ < δcompact :=
              lt_of_lt_of_le hsδ (min_le_right _ _)
            have hhalf : (η / 2) * ‖s‖ ≤ η * ‖s‖ := by
              nlinarith [hη, norm_nonneg s]
            exact (hcompact u hu s hscompact).trans hhalf
          · have hsone : ‖s‖ < 1 :=
              lt_of_lt_of_le hsδ (min_le_left _ _)
            have hu_norm : R + 1 < ‖u‖ := by
              simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hu
            have hu_eq_shifted : u = (u + s) - s := by ring
            have htriangle : ‖u‖ ≤ ‖u + s‖ + ‖s‖ := by
              calc
                ‖u‖ = ‖(u + s) - s‖ := congrArg norm hu_eq_shifted
                _ ≤ ‖u + s‖ + ‖s‖ := norm_sub_le _ _
            have hus_norm : R < ‖u + s‖ := by
              have hshift_lt :
                  ‖u + s‖ + ‖s‖ < ‖u + s‖ + 1 :=
                add_lt_add_right hsone ‖u + s‖
              have hsum_lt : R + 1 < ‖u + s‖ + 1 := by
                exact lt_trans (lt_of_lt_of_le hu_norm htriangle)
                  hshift_lt
              linarith
            have hu_ext : u ∉ Metric.closedBall (0 : ℝ) R := by
              simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using
                (lt_trans (lt_add_one R) hu_norm)
            have hus_ext : u + s ∉ Metric.closedBall (0 : ℝ) R := by
              simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using
                (not_le_of_gt hus_norm)
            have hu_zero : filteredEndpoint u = 0 :=
              hfilteredEndpoint_zero_exterior u hu_ext
            have hus_zero : filteredEndpoint (u + s) = 0 :=
              hfilteredEndpoint_zero_exterior (u + s) hus_ext
            rw [hu_zero, hus_zero]
            simp only [sub_self, zero_apply, smul_zero, norm_zero]
            exact mul_nonneg hη.le (norm_nonneg s)
        -- Infrastructure I.16 exact frontier: after top truncation removes all
        -- non-ones branches, the remaining all-ones branch must identify the
        -- predecessor defect at source `inverseCenter u` and transported
        -- increment `inverseCenter (u + s) - inverseCenter u`.
        -- The lower-order fixed-graph equation is first recorded as a finite
        -- jet identity.  Keeping this interface separate prevents the top
        -- coefficient calculation below from unfolding the graph equation.
        -- The exact predecessor recurrence has two regularity regimes.  At
        -- order one it follows from Taylor expansion along the actual graph
        -- chord together with the inverse-center Taylor remainder.  From order
        -- two onward the full finite jet of the actual center map absorbs all
        -- center-fiber feedback into a `C¹` forcing coefficient; its remaining
        -- all-ones term is precisely `principalOperator` applied to the
        -- transported predecessor defect.
        have hpredecessor_affineCocycle_certificate (η : ℝ) (hη : 0 < η) :
            ∃ δ > 0, ∀ u s : ℝ, s ≠ 0 → ‖s‖ < δ →
              ∃ contracted : X →L[ℝ] X, ∃ remainder : X,
                ‖contracted‖ ≤ p ∧
                rawTopDefect u s =
                    contracted
                      (rawTopDefect (inverseCenter u)
                        (inverseCenter (u + s) - inverseCenter u)) +
                      remainder ∧
                  ‖remainder‖ ≤ η * ‖s‖ := by
          have hderivativeValue_eq (y : ℝ) :
              derivativeValue y = a y oneTop := by
            dsimp only [derivativeValue, r]
            simp only [Nat.factorial_one, Nat.cast_one,
              one_smul]
          let candidateGraph (x : ℝ) : ℝ → X := fun z ↦
            ζ x + (z - x) • derivativeValue x
          have hcandidateGraph_contDiff (x : ℝ) :
              ContDiff ℝ 1 (candidateGraph x) := by
            dsimp only [candidateGraph]
            fun_prop
          have hcandidateGraph_hasDerivAt (x : ℝ) :
              HasDerivAt (candidateGraph x) (derivativeValue x) x := by
            dsimp only [candidateGraph]
            simpa only [id_eq, one_smul] using
              (((hasDerivAt_id' x).sub_const x).smul_const
                (derivativeValue x)).const_add (ζ x)
          let liveGraphJet : BoundedGraphJet X radius slope 1 :=
            JetTransform.topUpdatedGraphJet 1 hr_strict J₀ a
          have hliveJet_def (x : ℝ) :
              liveGraphJet.jet x =
                (JetTransform.topUpdatedGraphJet 1 hr_strict J₀ a).jet x :=
            rfl
          have hzero_lt_one : ((0 : Fin 2) : ℕ) < 1 := by
            norm_num
          have hliveJet_eq_model (x : ℝ) :
              liveGraphJet.jet x =
                FiniteTaylorJet.ofFunction ℝ 1 (candidateGraph x) x := by
            apply FiniteTaylorJet.ext_coeff
            intro n
            have hn_le : (n : ℕ) ≤ 1 := Nat.le_of_lt_succ n.isLt
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn_le with hn | hn
            · have hn_zero : n = (0 : Fin 2) := Fin.ext hn
              subst n
              rw [hliveJet_def]
              have hcoeff0 :
                  ((JetTransform.topUpdatedGraphJet 1 hr_strict J₀ a).jet x).coeff
                      (0 : Fin 2) =
                    (J₀.jet x).coeff (0 : Fin 2) :=
                JetTransform.topUpdatedGraphJet_coeff_of_lt
                  1 hr_strict J₀ a x (0 : Fin 2) hzero_lt_one
              rw [hcoeff0]
              rw [hJ₀_lower x (0 : Fin 2) hzero_lt_one]
              apply ContinuousMultilinearMap.ext
              intro z
              have hz : z = 0 := by
                funext i
                exact Fin.elim0 i
              calc
                (FiniteTaylorJet.ofFunction ℝ 1 (ζ : ℝ → X) x).coeff
                      (0 : Fin 2) z =
                    (FiniteTaylorJet.ofFunction ℝ 1
                      (ζ : ℝ → X) x).constantCoeff := by
                  rw [hz]
                  exact (FiniteTaylorJet.constantCoeff_eq_coeff_zero _).symm
                _ = ζ x :=
                  FiniteTaylorJet.constantCoeff_ofFunction 1
                    (ζ : ℝ → X) x
                _ = candidateGraph x x := by
                  simp only [candidateGraph, sub_self, zero_smul, add_zero]
                _ = (FiniteTaylorJet.ofFunction ℝ 1
                      (candidateGraph x) x).constantCoeff :=
                  (FiniteTaylorJet.constantCoeff_ofFunction 1
                    (candidateGraph x) x).symm
                _ = (FiniteTaylorJet.ofFunction ℝ 1
                      (candidateGraph x) x).coeff (0 : Fin 2) z := by
                  rw [hz]
                  exact FiniteTaylorJet.constantCoeff_eq_coeff_zero _
            · have hn_one : n = (1 : Fin 2) := Fin.ext hn
              subst n
              rw [hliveJet_def]
              change
                ((JetTransform.topUpdatedGraphJet 1 hr_strict J₀ a).jet x).coeff
                    ⟨1, Nat.lt_succ_self 1⟩ =
                  (FiniteTaylorJet.ofFunction ℝ 1
                    (candidateGraph x) x).coeff
                    ⟨1, Nat.lt_succ_self 1⟩
              rw [JetTransform.topUpdatedGraphJet_topCoeff]
              apply ContinuousMultilinearMap.ext
              intro z
              have hz : z = (z 0) • oneTop := by
                funext i
                rw [Fin.eq_zero i]
                simp only [Pi.smul_apply, smul_eq_mul, oneTop, mul_one]
              have hscaledOneTop :
                  (z 0) • oneTop = fun _ : Fin 1 ↦ z 0 := by
                funext i
                simp only [Pi.smul_apply, smul_eq_mul, oneTop, mul_one]
              have honeTop_coefficient :
                  a x oneTop =
                    (FiniteTaylorJet.ofFunction ℝ 1
                      (candidateGraph x) x).coeff
                        ⟨1, Nat.lt_succ_self 1⟩ oneTop := by
                rw [← hderivativeValue_eq x]
                rw [FiniteTaylorJet.coeff_ofFunction_apply]
                simp only [Nat.factorial_one, Nat.cast_one, inv_one,
                  one_smul, iteratedFDeriv_one_apply]
                rw [(hcandidateGraph_hasDerivAt x).hasFDerivAt.fderiv]
                simp only [
                  ContinuousLinearMap.toSpanSingleton_apply]
                simp only [oneTop, one_smul]
              have haScale := (a x).map_smul_univ
                (fun _ : Fin 1 ↦ z 0) (fun _ : Fin 1 ↦ (1 : ℝ))
              have hjScale :=
                ((FiniteTaylorJet.ofFunction ℝ 1
                  (candidateGraph x) x).coeff
                    ⟨1, Nat.lt_succ_self 1⟩).map_smul_univ
                  (fun _ : Fin 1 ↦ z 0) (fun _ : Fin 1 ↦ (1 : ℝ))
              rw [hz]
              calc
                a x ((z 0) • oneTop) =
                    (z 0) • a x oneTop := by
                  rw [hscaledOneTop]
                  simpa only [oneTop, smul_eq_mul, mul_one,
                    Finset.prod_const, Finset.card_fin, pow_one] using haScale
                _ = (z 0) •
                    (FiniteTaylorJet.ofFunction ℝ 1
                      (candidateGraph x) x).coeff
                        ⟨1, Nat.lt_succ_self 1⟩ oneTop :=
                  congrArg (fun w : X ↦ (z 0) • w) honeTop_coefficient
                _ = (FiniteTaylorJet.ofFunction ℝ 1
                      (candidateGraph x) x).coeff
                        ⟨1, Nat.lt_succ_self 1⟩ ((z 0) • oneTop) := by
                  symm
                  rw [hscaledOneTop]
                  simpa only [oneTop, smul_eq_mul, mul_one,
                    Finset.prod_const, Finset.card_fin, pow_one] using hjScale
          let candidateParam (x : ℝ) : ℝ → ℝ × X := fun z ↦
            (z, candidateGraph x z)
          have hcandidateParam_contDiff (x : ℝ) :
              ContDiff ℝ 1 (candidateParam x) := by
            dsimp only [candidateParam]
            exact contDiff_id.prodMk (hcandidateGraph_contDiff x)
          have hgraphParam_eq_model (x : ℝ) :
              JetTransform.graphParametrizationJet 1 liveGraphJet x =
                FiniteTaylorJet.ofFunction ℝ 1 (candidateParam x) x := by
            calc
              JetTransform.graphParametrizationJet 1 liveGraphJet x =
                  FiniteTaylorJet.prod
                    (FiniteTaylorJet.ofFunction ℝ 1 id x)
                    (FiniteTaylorJet.ofFunction ℝ 1 (candidateGraph x) x) := by
                rw [JetTransform.graphParametrizationJet,
                  hliveJet_eq_model]
              _ = FiniteTaylorJet.ofFunction ℝ 1 (candidateParam x) x := by
                simpa only [candidateParam, id_eq] using
                  (FiniteTaylorJet.ofFunction_prodMk
                    (m := 1) (a := x) contDiffAt_id
                    (hcandidateGraph_contDiff x).contDiffAt).symm
          let imagePath (x : ℝ) : ℝ → ℝ × X := fun z ↦
            LocalCutoff.centerStableLinearize χ ρ L N (candidateParam x z)
          have himagePath_contDiff (x : ℝ) :
              ContDiff ℝ 1 (imagePath x) := by
            dsimp only [imagePath]
            exact hlinearize_smooth_fixed.comp (hcandidateParam_contDiff x)
          have himageJet_eq_model (x : ℝ) :
              JetTransform.imageJet 1 χ ρ L N liveGraphJet x =
                FiniteTaylorJet.ofFunction ℝ 1 (imagePath x) x := by
            rw [JetTransform.imageJet, FiniteTaylorJet.postcomp_def,
              hgraphParam_eq_model,
              FiniteTaylorJet.constantCoeff_ofFunction]
            simpa only [imagePath, Function.comp_def] using
              (FiniteTaylorJet.comp_ofFunction_one
                (f := candidateParam x)
                (g := LocalCutoff.centerStableLinearize χ ρ L N)
                (x := x) (hcandidateParam_contDiff x).contDiffAt
                hlinearize_smooth_fixed.contDiffAt)
          let stablePath (x : ℝ) : ℝ → X := fun z ↦ (imagePath x z).2
          have hstablePath_contDiff (x : ℝ) :
              ContDiff ℝ 1 (stablePath x) := by
            dsimp only [stablePath]
            exact (himagePath_contDiff x).snd
          have hstableJet_eq_model (x : ℝ) :
              JetTransform.stableJet 1 χ ρ L N liveGraphJet x =
                FiniteTaylorJet.ofFunction ℝ 1 (stablePath x) x := by
            rw [JetTransform.stableJet, FiniteTaylorJet.postcomp_def,
              himageJet_eq_model,
              FiniteTaylorJet.constantCoeff_ofFunction]
            simpa only [stablePath, Function.comp_def] using
              (FiniteTaylorJet.comp_ofFunction_one
                (f := imagePath x) (g := Prod.snd) (x := x)
                (himagePath_contDiff x).contDiffAt contDiffAt_snd)
          have htwo_le_nu :
              (2 : WithTop ENat) ≤ (ν : WithTop ENat) := by
            exact_mod_cast hν
          have htwo_order_pos : 1 ≤ (2 : ℕ) := by
            norm_num
          have hinverseCenter_contDiff_two : ContDiff ℝ 2 inverseCenter := by
            dsimp only [inverseCenter]
            rw [LocalCutoff.CenterProjection.inverse_def]
            apply Real.contDiff_invFun_of_pos_le_deriv
            · exact (h_center_smooth ζ).of_le htwo_le_nu
            · exact htwo_order_pos
            · exact h_lower_pos
            · exact h_lower ζ
          have hone_le_two :
              (1 : WithTop ENat) ≤ (2 : WithTop ENat) := by
            norm_num
          have hinverseCenter_contDiff_one : ContDiff ℝ 1 inverseCenter :=
            hinverseCenter_contDiff_two.of_le hone_le_two
          have hfixedEndpoint_eq_model (x : ℝ) :
              fixedEndpoint
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x) =
                (FiniteTaylorJet.ofFunction ℝ 1
                  (stablePath x ∘ inverseCenter)
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x)).coeff
                  ⟨1, Nat.lt_succ_self 1⟩ := by
            have hstablePath_contDiffAt_inverse :
                ContDiffAt ℝ 1 (stablePath x)
                  (inverseCenter
                    (LocalCutoff.CenterProjection.map χ ρ L N ζ x)) := by
              simpa only [hinverseCenter_forward] using
                (hstablePath_contDiff x).contDiffAt
            dsimp only [fixedEndpoint, r]
            rw [hinverseCenter_forward, hstableJet_eq_model]
            simpa only [hinverseCenter_forward] using
              congrArg
                (fun Q : FiniteTaylorJet ℝ ℝ X 1 ↦
                  Q.coeff ⟨1, Nat.lt_succ_self 1⟩)
                (FiniteTaylorJet.comp_ofFunction_one
                  (f := inverseCenter) (g := stablePath x)
                  (x := LocalCutoff.CenterProjection.map χ ρ L N ζ x)
                  hinverseCenter_contDiff_one.contDiffAt
                  hstablePath_contDiffAt_inverse)
          let stableOutput : ℝ × X → X := fun point ↦
            (LocalCutoff.centerStableLinearize χ ρ L N point).2
          have hlinearize_contDiff_two :
              ContDiff ℝ 2
                (LocalCutoff.centerStableLinearize χ ρ L N) := by
            have hcutoff_contDiff_nu : ContDiff ℝ ν
                (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) :=
              hχ_smooth.comp (contDiff_const_smul ρ⁻¹)
            have hremainder_eq :
                LocalCutoff.remainder χ ρ N =
                  (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) • N := by
              funext point
              exact LocalCutoff.remainder_apply χ ρ N point
            have hremainder_contDiff_nu : ContDiff ℝ ν
                (LocalCutoff.remainder χ ρ N) := by
              rw [hremainder_eq]
              exact hcutoff_contDiff_nu.smul hN_smooth
            have hlinearize_eq :
                LocalCutoff.centerStableLinearize χ ρ L N =
                  LocalCutoff.centerStable L +
                    LocalCutoff.remainder χ ρ N := by
              funext point
              rw [Pi.add_apply,
                LocalCutoff.centerStableLinearize_apply,
                LocalCutoff.remainder_apply]
            have hlinearize_contDiff_nu : ContDiff ℝ ν
                (LocalCutoff.centerStableLinearize χ ρ L N) := by
              rw [hlinearize_eq]
              exact (LocalCutoff.centerStable L).contDiff.add
                hremainder_contDiff_nu
            exact hlinearize_contDiff_nu.of_le htwo_le_nu
          have hstableOutput_contDiff_two :
              ContDiff ℝ 2 stableOutput := by
            dsimp only [stableOutput]
            exact hlinearize_contDiff_two.snd
          have hstableOutput_contDiff : ContDiff ℝ 1 stableOutput :=
            hstableOutput_contDiff_two.of_le hone_le_two
          have hcandidateParam_hasDerivAt (x : ℝ) :
              HasDerivAt (candidateParam x) (1, derivativeValue x) x := by
            dsimp only [candidateParam]
            exact (hasDerivAt_id x).prodMk (hcandidateGraph_hasDerivAt x)
          have hstablePath_hasDerivAt (x : ℝ) :
              HasDerivAt (stablePath x)
                (fderiv ℝ stableOutput (x, ζ x) (1, derivativeValue x)) x := by
            have hcandidateParam_self :
                candidateParam x x = (x, ζ x) := by
              simp only [candidateParam, candidateGraph, sub_self, zero_smul,
                add_zero]
            have houter : HasFDerivAt stableOutput
                (fderiv ℝ stableOutput (x, ζ x)) (x, ζ x) :=
              (hstableOutput_contDiff.differentiable one_ne_zero
                (x, ζ x)).hasFDerivAt
            have houterAtCandidate : HasFDerivAt stableOutput
                (fderiv ℝ stableOutput (x, ζ x))
                  (candidateParam x x) := by
              rw [hcandidateParam_self]
              exact houter
            have hcomp := houterAtCandidate.comp_hasDerivAt x
              (hcandidateParam_hasDerivAt x)
            simpa only [stablePath, imagePath, stableOutput, candidateParam,
              candidateGraph, Function.comp_def, sub_self, zero_smul,
              add_zero] using hcomp
          have hstableComposite_hasDerivAt (x : ℝ) :
              HasDerivAt (stablePath x ∘ inverseCenter)
                ((deriv inverseCenter
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x)) •
                  fderiv ℝ stableOutput (x, ζ x) (1, derivativeValue x))
                (LocalCutoff.CenterProjection.map χ ρ L N ζ x) := by
            have hinverse :=
              (hinverseCenter_contDiff_one.differentiable one_ne_zero
                (LocalCutoff.CenterProjection.map χ ρ L N ζ x)).hasDerivAt
            have hcomp := (hstablePath_hasDerivAt x).scomp_of_eq
              (LocalCutoff.CenterProjection.map χ ρ L N ζ x) hinverse
              (hinverseCenter_forward x).symm
            exact hcomp
          have hfixedEndpoint_apply_one (x : ℝ) :
              fixedEndpoint
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x) oneTop =
                (deriv inverseCenter
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x)) •
                  fderiv ℝ stableOutput (x, ζ x)
                    (1, derivativeValue x) := by
            rw [hfixedEndpoint_eq_model]
            rw [FiniteTaylorJet.coeff_ofFunction_apply]
            simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
              iteratedFDeriv_one_apply]
            rw [(hstableComposite_hasDerivAt x).hasFDerivAt.fderiv]
            simp only [
              ContinuousLinearMap.toSpanSingleton_apply]
            simp only [oneTop, one_smul]
          have horderOne_fixed_linearization (x : ℝ) :
              derivativeValue
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x) =
                (deriv inverseCenter
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x)) •
                  fderiv ℝ stableOutput (x, ζ x)
                    (1, derivativeValue x) := by
            calc
              derivativeValue
                  (LocalCutoff.CenterProjection.map χ ρ L N ζ x) =
                  fixedEndpoint
                    (LocalCutoff.CenterProjection.map χ ρ L N ζ x) oneTop := by
                simpa only [r, Nat.factorial_one, Nat.cast_one, one_smul] using
                  hderivativeValue_forward x
              _ = _ := hfixedEndpoint_apply_one x
          have htwo_nat_ne : (2 : ℕ) ≠ 0 := by
            norm_num
          have htwo_cast_ne :
              ((2 : ℕ) : WithTop ENat) ≠ 0 :=
            Nat.cast_ne_zero.mpr htwo_nat_ne
          have hcutoffRemainder_contDiff_two : ContDiff ℝ 2
              (LocalCutoff.remainder χ ρ N) := by
            have hcutoff_contDiff_nu : ContDiff ℝ ν
                (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) :=
              hχ_smooth.comp (contDiff_const_smul ρ⁻¹)
            have hremainder_eq :
                LocalCutoff.remainder χ ρ N =
                  (fun point : ℝ × X ↦ χ (ρ⁻¹ • point)) • N := by
              funext point
              exact LocalCutoff.remainder_apply χ ρ N point
            have hremainder_contDiff_nu : ContDiff ℝ ν
                (LocalCutoff.remainder χ ρ N) := by
              rw [hremainder_eq]
              exact hcutoff_contDiff_nu.smul hN_smooth
            exact hremainder_contDiff_nu.of_le htwo_le_nu
          have hcutoffRemainder_differentiable : Differentiable ℝ
              (LocalCutoff.remainder χ ρ N) :=
            hcutoffRemainder_contDiff_two.differentiable htwo_cast_ne
          have hcutoffRemainder_fderiv_uniformContinuous :
              UniformContinuous
                (fderiv ℝ (LocalCutoff.remainder χ ρ N)) := by
            have hcontinuous : Continuous
                (fderiv ℝ (LocalCutoff.remainder χ ρ N)) :=
              hcutoffRemainder_contDiff_two.continuous_fderiv htwo_cast_ne
            have hsupport : HasCompactSupport
                (fderiv ℝ (LocalCutoff.remainder χ ρ N)) :=
              (LocalCutoff.hasCompactSupport_remainder χ ρ N hρ
                hχ_support).fderiv ℝ
            exact hcontinuous.uniformContinuous_of_tendsto_cocompact
              hsupport.is_zero_at_infty
          have hlinearize_eq :
              LocalCutoff.centerStableLinearize χ ρ L N =
                LocalCutoff.centerStable L +
                  LocalCutoff.remainder χ ρ N := by
            funext point
            rw [Pi.add_apply, LocalCutoff.centerStableLinearize_apply,
              LocalCutoff.remainder_apply]
          have hlinearize_differentiable : Differentiable ℝ
              (LocalCutoff.centerStableLinearize χ ρ L N) :=
            hlinearize_contDiff_two.differentiable htwo_cast_ne
          have hlinearize_fderiv_eq (point : ℝ × X) :
              fderiv ℝ (LocalCutoff.centerStableLinearize χ ρ L N) point =
                LocalCutoff.centerStable L +
                  fderiv ℝ (LocalCutoff.remainder χ ρ N) point := by
            have hadd := (LocalCutoff.centerStable L).hasFDerivAt.add
              (hcutoffRemainder_differentiable point).hasFDerivAt
            rw [hlinearize_eq]
            exact hadd.fderiv
          have hlinearize_fderiv_uniformContinuous : UniformContinuous
              (fderiv ℝ
                (LocalCutoff.centerStableLinearize χ ρ L N)) := by
            have hderiv_function :
                fderiv ℝ
                    (LocalCutoff.centerStableLinearize χ ρ L N) =
                  fun point ↦ LocalCutoff.centerStable L +
                    fderiv ℝ (LocalCutoff.remainder χ ρ N) point := by
              funext point
              exact hlinearize_fderiv_eq point
            rw [hderiv_function]
            exact uniformContinuous_const.add
              hcutoffRemainder_fderiv_uniformContinuous
          have hstableOutput_fderiv (point : ℝ × X) :
              fderiv ℝ stableOutput point =
                (ContinuousLinearMap.snd ℝ ℝ X).comp
                  (fderiv ℝ
                    (LocalCutoff.centerStableLinearize χ ρ L N) point) := by
            exact fderiv.snd (hlinearize_differentiable point)
          let graphScale : ℝ := max 1 (slope : ℝ)
          have hgraphScale_pos : 0 < graphScale := by
            exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (slope : ℝ))
          have hgraphIncrement_norm_le (x h : ℝ) :
              ‖((h : ℝ), ζ (x + h) - ζ x)‖ ≤
                graphScale * ‖h‖ := by
            have hgraph :=
              (SmallLipschitzGraph.lipschitzWith ζ).dist_le_mul (x + h) x
            have hgraph_chord :
                ‖ζ (x + h) - ζ x‖ ≤ (slope : ℝ) * ‖h‖ := by
              simpa only [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs,
                add_sub_cancel_left] using hgraph
            have hcenter_bound : ‖h‖ ≤ graphScale * ‖h‖ := by
              calc
                ‖h‖ = 1 * ‖h‖ := by rw [one_mul]
                _ ≤ graphScale * ‖h‖ :=
                  mul_le_mul_of_nonneg_right (le_max_left _ _)
                    (norm_nonneg h)
            have hstable_bound :
                ‖ζ (x + h) - ζ x‖ ≤ graphScale * ‖h‖ := by
              exact hgraph_chord.trans
                (mul_le_mul_of_nonneg_right (le_max_right _ _)
                  (norm_nonneg h))
            rw [Prod.norm_def]
            exact max_le hcenter_bound hstable_bound
          have hstableTaylorRate_pos :
              0 < η / (2 * graphScale * c) := by
            positivity
          obtain ⟨δStable, hδStable_pos, hδStable⟩ :=
            uniformFirstOrderRemainder_of_uniformContinuous_fderiv
              hlinearize_differentiable
              hlinearize_fderiv_uniformContinuous hstableTaylorRate_pos
          have hδStableScalar_pos : 0 < δStable / graphScale := by
            positivity
          have hstableGraphRemainder (x h : ℝ)
              (hh : ‖h‖ < δStable / graphScale) :
              ‖stableOutput (x + h, ζ (x + h)) -
                  stableOutput (x, ζ x) -
                  fderiv ℝ stableOutput (x, ζ x)
                    (h, ζ (x + h) - ζ x)‖ ≤
                (η / (2 * c)) * ‖h‖ := by
            let graphIncrement : ℝ × X :=
              (h, ζ (x + h) - ζ x)
            have hgraphIncrement_lt : ‖graphIncrement‖ < δStable := by
              calc
                ‖graphIncrement‖ ≤ graphScale * ‖h‖ := by
                  exact hgraphIncrement_norm_le x h
                _ < graphScale * (δStable / graphScale) :=
                  mul_lt_mul_of_pos_left hh hgraphScale_pos
                _ = δStable := by
                  field_simp [hgraphScale_pos.ne']
            have hpoint_add :
                (x, ζ x) + graphIncrement = (x + h, ζ (x + h)) := by
              apply Prod.ext
              · rfl
              · dsimp only [graphIncrement]
                simp only [Prod.snd_add]
                abel
            have hfull := hδStable (x, ζ x) graphIncrement
              hgraphIncrement_lt
            rw [hpoint_add] at hfull
            have hcomponent_identity :
                stableOutput (x + h, ζ (x + h)) -
                    stableOutput (x, ζ x) -
                    fderiv ℝ stableOutput (x, ζ x)
                      (h, ζ (x + h) - ζ x) =
                  (LocalCutoff.centerStableLinearize χ ρ L N
                      (x + h, ζ (x + h)) -
                    LocalCutoff.centerStableLinearize χ ρ L N (x, ζ x) -
                    fderiv ℝ
                      (LocalCutoff.centerStableLinearize χ ρ L N)
                      (x, ζ x) graphIncrement).2 := by
              rw [hstableOutput_fderiv]
              rfl
            rw [hcomponent_identity]
            have hcomponent := (norm_snd_le _).trans hfull
            have hscaled := hcomponent.trans
              (mul_le_mul_of_nonneg_left
                (hgraphIncrement_norm_le x h) hstableTaylorRate_pos.le)
            have hrate_identity :
                η / (2 * graphScale * c) *
                    (graphScale * ‖h‖) =
                  (η / (2 * c)) * ‖h‖ := by
              field_simp [hgraphScale_pos.ne', hc_pos.ne']
            rw [hrate_identity] at hscaled
            exact hscaled
          let stableJointRate : ℝ≥0 :=
            linearRate + stableCenter + stableFiber
          have hstableOutput_lipschitz :
              LipschitzWith stableJointRate stableOutput := by
            apply LipschitzWith.of_dist_le_mul
            intro point other
            have hout (q : ℝ × X) :
                stableOutput q = L q.2 +
                  (LocalCutoff.remainder χ ρ N q).2 := by
              rcases q with ⟨v, z⟩
              dsimp only [stableOutput]
              rw [LocalCutoff.centerStableLinearize_apply,
                LocalCutoff.centerStable_apply]
              change L z + (χ (ρ⁻¹ • (v, z)) • N (v, z)).2 = _
              rw [LocalCutoff.remainder_apply]
            have hlinear : ‖L point.2 - L other.2‖ ≤
                (linearRate : ℝ) * ‖point.2 - other.2‖ := by
              rw [← map_sub]
              exact (L.le_opNorm _).trans
                (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
            have hstable := h_stable_lipschitz point.1 other.1
              point.2 other.2
            have hfirst : |point.1 - other.1| ≤ ‖point - other‖ := by
              simpa only [Prod.fst_sub, Real.norm_eq_abs] using
                (norm_fst_le (point - other))
            have hsecond : ‖point.2 - other.2‖ ≤ ‖point - other‖ := by
              simpa only [Prod.snd_sub] using
                (norm_snd_le (point - other))
            rw [dist_eq_norm, hout point, hout other]
            calc
              ‖(L point.2 + (LocalCutoff.remainder χ ρ N point).2) -
                  (L other.2 +
                    (LocalCutoff.remainder χ ρ N other).2)‖ =
                  ‖(L point.2 - L other.2) +
                    ((LocalCutoff.remainder χ ρ N point).2 -
                      (LocalCutoff.remainder χ ρ N other).2)‖ := by
                congr 1
                abel
              _ ≤ ‖L point.2 - L other.2‖ +
                  ‖(LocalCutoff.remainder χ ρ N point).2 -
                    (LocalCutoff.remainder χ ρ N other).2‖ :=
                norm_add_le _ _
              _ ≤ (linearRate : ℝ) * ‖point.2 - other.2‖ +
                  ((stableCenter : ℝ) * |point.1 - other.1| +
                    (stableFiber : ℝ) * ‖point.2 - other.2‖) :=
                add_le_add hlinear hstable
              _ ≤ (linearRate : ℝ) * ‖point - other‖ +
                  ((stableCenter : ℝ) * ‖point - other‖ +
                    (stableFiber : ℝ) * ‖point - other‖) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hsecond linearRate.coe_nonneg)
                  (add_le_add
                    (mul_le_mul_of_nonneg_left hfirst
                      stableCenter.coe_nonneg)
                    (mul_le_mul_of_nonneg_left hsecond
                      stableFiber.coe_nonneg))
              _ = (stableJointRate : ℝ) * ‖point - other‖ := by
                simp only [stableJointRate, NNReal.coe_add]
                ring
              _ = (stableJointRate : ℝ) * dist point other := by
                rw [dist_eq_norm]
          have hstableOutput_fderiv_norm_le (point : ℝ × X) :
              ‖fderiv ℝ stableOutput point‖ ≤ (stableJointRate : ℝ) :=
            norm_fderiv_le_of_lipschitz ℝ hstableOutput_lipschitz
          have hderivativeValue_norm_le_one (x : ℝ) :
              ‖derivativeValue x‖ ≤ ‖a‖ := by
            rw [hderivativeValue_eq]
            calc
              ‖a x oneTop‖ ≤ ‖a x‖ * ∏ i : Fin 1, ‖oneTop i‖ :=
                ContinuousMultilinearMap.le_opNorm (a x) oneTop
              _ = ‖a x‖ := by
                simp only [oneTop, norm_one, Finset.prod_const_one,
                  mul_one]
              _ ≤ ‖a‖ := BoundedContinuousFunction.norm_coe_le_norm a x
          have hcandidateDirection_norm_le (x : ℝ) :
              ‖((1 : ℝ), derivativeValue x)‖ ≤ 1 + ‖a‖ := by
            rw [Prod.norm_def]
            apply max_le
            · simp only [norm_one]
              exact le_add_of_nonneg_right (norm_nonneg a)
            · exact (hderivativeValue_norm_le_one x).trans
                (le_add_of_nonneg_left zero_le_one)
          let stableLinearization (x : ℝ) : X :=
            fderiv ℝ stableOutput (x, ζ x) (1, derivativeValue x)
          let stableLinearizationBound : ℝ :=
            (stableJointRate : ℝ) * (1 + ‖a‖) + 1
          have hstableLinearizationBound_pos :
              0 < stableLinearizationBound := by
            dsimp only [stableLinearizationBound]
            positivity
          have hstableLinearization_norm_le (x : ℝ) :
              ‖stableLinearization x‖ ≤ stableLinearizationBound := by
            calc
              ‖stableLinearization x‖ ≤
                  ‖fderiv ℝ stableOutput (x, ζ x)‖ *
                    ‖((1 : ℝ), derivativeValue x)‖ :=
                (fderiv ℝ stableOutput (x, ζ x)).le_opNorm _
              _ ≤ (stableJointRate : ℝ) * (1 + ‖a‖) := by
                gcongr
                exact hstableOutput_fderiv_norm_le (x, ζ x)
                exact hcandidateDirection_norm_le x
              _ ≤ (stableJointRate : ℝ) * (1 + ‖a‖) + 1 := by
                linarith
              _ = stableLinearizationBound := rfl
          have hinverseCenter_eq_self_outside (z : ℝ)
              (hz : z ∉ Metric.closedBall (0 : ℝ) R) :
              inverseCenter z = z := by
            have hR_lt : R < |z| := by
              simpa only [Metric.mem_closedBall, dist_zero_right,
                Real.norm_eq_abs, not_le] using hz
            have hRmap_le : Rmap ≤ |z| :=
              (le_max_right _ _).trans hR_lt.le
            apply (hcenter_bijective ζ).1
            rw [hforwardCenter_inverse, hRmap_eq ζ z hRmap_le]
          let inversePerturbation : ℝ → ℝ := fun z ↦ inverseCenter z - z
          have hinversePerturbation_contDiff_two :
              ContDiff ℝ 2 inversePerturbation := by
            dsimp only [inversePerturbation]
            exact hinverseCenter_contDiff_two.sub contDiff_id
          have hinversePerturbation_support :
              HasCompactSupport inversePerturbation := by
            apply HasCompactSupport.intro
              (isCompact_closedBall (0 : ℝ) R)
            intro z hz
            dsimp only [inversePerturbation]
            rw [hinverseCenter_eq_self_outside z hz, sub_self]
          have hinversePerturbation_differentiable :
              Differentiable ℝ inversePerturbation :=
            hinversePerturbation_contDiff_two.differentiable htwo_cast_ne
          have hinversePerturbation_fderiv_uniformContinuous :
              UniformContinuous (fderiv ℝ inversePerturbation) := by
            have hcontinuous : Continuous
                (fderiv ℝ inversePerturbation) :=
              hinversePerturbation_contDiff_two.continuous_fderiv
                htwo_cast_ne
            have hsupport : HasCompactSupport
                (fderiv ℝ inversePerturbation) :=
              hinversePerturbation_support.fderiv ℝ
            exact hcontinuous.uniformContinuous_of_tendsto_cocompact
              hsupport.is_zero_at_infty
          have hinverse_eq_id_add_perturbation :
              inverseCenter =
                fun z : ℝ ↦ z + inversePerturbation z := by
            funext z
            dsimp only [inversePerturbation]
            ring
          have hinverse_fderiv_eq (z : ℝ) :
              fderiv ℝ inverseCenter z =
                ContinuousLinearMap.id ℝ ℝ +
                  fderiv ℝ inversePerturbation z := by
            rw [hinverse_eq_id_add_perturbation]
            exact ((hasFDerivAt_id z).add
              (hinversePerturbation_differentiable z).hasFDerivAt).fderiv
          have hinverse_fderiv_uniformContinuous :
              UniformContinuous (fderiv ℝ inverseCenter) := by
            have hderiv_function :
                fderiv ℝ inverseCenter = fun z ↦
                  ContinuousLinearMap.id ℝ ℝ +
                    fderiv ℝ inversePerturbation z := by
              funext z
              exact hinverse_fderiv_eq z
            rw [hderiv_function]
            exact uniformContinuous_const.add
              hinversePerturbation_fderiv_uniformContinuous
          have hinverse_differentiable : Differentiable ℝ inverseCenter :=
            hinverseCenter_contDiff_two.differentiable htwo_cast_ne
          have hinverseTaylorRate_pos :
              0 < η / (2 * stableLinearizationBound) := by
            positivity
          obtain ⟨δInverse, hδInverse_pos, hδInverse⟩ :=
            uniformFirstOrderRemainder_of_uniformContinuous_fderiv
              hinverse_differentiable hinverse_fderiv_uniformContinuous
              hinverseTaylorRate_pos
          have hinverseRemainder (u s : ℝ) (hs : ‖s‖ < δInverse) :
              ‖inverseCenter (u + s) - inverseCenter u -
                  s • deriv inverseCenter u‖ ≤
                (η / (2 * stableLinearizationBound)) * ‖s‖ := by
            simpa only [fderiv_eq_smul_deriv] using
              hδInverse u s hs
          have hinverseIncrement_norm_le (u s : ℝ) :
              ‖inverseCenter (u + s) - inverseCenter u‖ ≤ c * ‖s‖ := by
            calc
              ‖inverseCenter (u + s) - inverseCenter u‖ =
                  dist (inverseCenter (u + s)) (inverseCenter u) := by
                rw [dist_eq_norm]
              _ ≤ (lower⁻¹ : ℝ) * dist (u + s) u :=
                (hcenter_inverse_lipschitz ζ).dist_le_mul _ _
              _ = c * ‖s‖ := by
                rw [dist_eq_norm, add_sub_cancel_left]
                rfl
          have hstableFiber_fderiv (u : ℝ) :
              fderiv ℝ
                  (fun z : X ↦
                    (LocalCutoff.centerStableLinearize χ ρ L N
                      (inverseCenter u, z)).2)
                  (ζ (inverseCenter u)) =
                (fderiv ℝ stableOutput
                  (inverseCenter u, ζ (inverseCenter u))).comp
                    (ContinuousLinearMap.inr ℝ ℝ X) := by
            have houter : HasFDerivAt stableOutput
                (fderiv ℝ stableOutput
                  (inverseCenter u, ζ (inverseCenter u)))
                (inverseCenter u, ζ (inverseCenter u)) :=
              (hstableOutput_contDiff.differentiable one_ne_zero
                (inverseCenter u, ζ (inverseCenter u))).hasFDerivAt
            have hcomp := houter.comp (ζ (inverseCenter u))
              (hasFDerivAt_prodMk_right (inverseCenter u)
                (ζ (inverseCenter u)))
            have hslice_eq :
                (fun z : X ↦
                  (LocalCutoff.centerStableLinearize χ ρ L N
                    (inverseCenter u, z)).2) =
                  stableOutput ∘ Prod.mk (inverseCenter u) := by
              rfl
            rw [hslice_eq]
            exact hcomp.fderiv
          have hprincipalOperator_apply (u : ℝ) (w : X) :
              principalOperator u w =
                fderiv ℝ stableOutput
                  (inverseCenter u, ζ (inverseCenter u)) (0, w) := by
            dsimp only [principalOperator, r]
            simp only [Nat.sub_self, pow_zero, one_smul]
            rw [hstableFiber_fderiv]
            rfl
          let δ : ℝ := min δInverse ((δStable / graphScale) / c)
          have hδ_pos : 0 < δ := by
            dsimp only [δ]
            exact lt_min hδInverse_pos (div_pos hδStableScalar_pos hc_pos)
          refine ⟨δ, hδ_pos, ?_⟩
          intro u s _hs hsδ
          have hs_inverse : ‖s‖ < δInverse :=
            lt_of_lt_of_le hsδ (min_le_left _ _)
          have hs_stable : ‖s‖ < (δStable / graphScale) / c :=
            lt_of_lt_of_le hsδ (min_le_right _ _)
          let sourceBase : ℝ := inverseCenter u
          let sourceIncrement : ℝ :=
            inverseCenter (u + s) - inverseCenter u
          let sourceDefect : X :=
            rawTopDefect sourceBase sourceIncrement
          let sourceLinearization : X :=
            stableLinearization sourceBase
          let stableError : X :=
            stableOutput
                  (sourceBase + sourceIncrement,
                    ζ (sourceBase + sourceIncrement)) -
              stableOutput (sourceBase, ζ sourceBase) -
              fderiv ℝ stableOutput (sourceBase, ζ sourceBase)
                (sourceIncrement,
                  ζ (sourceBase + sourceIncrement) - ζ sourceBase)
          let inverseError : ℝ :=
            sourceIncrement - s • deriv inverseCenter u
          let remainder : X :=
            stableError + inverseError • sourceLinearization
          have hsource_endpoint :
              sourceBase + sourceIncrement = inverseCenter (u + s) := by
            dsimp only [sourceBase, sourceIncrement]
            ring
          have hsource_forward :
              LocalCutoff.CenterProjection.map χ ρ L N ζ sourceBase = u := by
            dsimp only [sourceBase]
            exact hforwardCenter_inverse u
          have hsourceIncrement_norm :
              ‖sourceIncrement‖ ≤ c * ‖s‖ := by
            simpa only [sourceIncrement] using
              hinverseIncrement_norm_le u s
          have hsourceIncrement_small :
              ‖sourceIncrement‖ < δStable / graphScale := by
            calc
              ‖sourceIncrement‖ ≤ c * ‖s‖ := hsourceIncrement_norm
              _ < c * ((δStable / graphScale) / c) :=
                mul_lt_mul_of_pos_left hs_stable hc_pos
              _ = δStable / graphScale := by
                field_simp [hc_pos.ne']
          have hsourceDefect_eq :
              sourceDefect =
                ζ (sourceBase + sourceIncrement) - ζ sourceBase -
                  sourceIncrement • derivativeValue sourceBase := by
            simp only [sourceDefect, rawTopDefect, predecessorValue, r,
              Nat.sub_self, iteratedDeriv_zero]
          have hgraphDirection :
              (sourceIncrement,
                  ζ (sourceBase + sourceIncrement) - ζ sourceBase) =
                sourceIncrement •
                    ((1 : ℝ), derivativeValue sourceBase) +
                  (0, sourceDefect) := by
            apply Prod.ext
            · change sourceIncrement = sourceIncrement * 1 + 0
              ring
            · change
                ζ (sourceBase + sourceIncrement) - ζ sourceBase =
                  sourceIncrement • derivativeValue sourceBase + sourceDefect
              rw [hsourceDefect_eq]
              abel
          have hlinearizedGraphDirection :
              fderiv ℝ stableOutput (sourceBase, ζ sourceBase)
                  (sourceIncrement,
                    ζ (sourceBase + sourceIncrement) - ζ sourceBase) =
                sourceIncrement • sourceLinearization +
                  principalOperator u sourceDefect := by
            rw [hgraphDirection, map_add, map_smul]
            dsimp only [sourceLinearization, stableLinearization, sourceBase]
            rw [hprincipalOperator_apply]
          have hfixedLinearization_source :
              derivativeValue u =
                deriv inverseCenter u • sourceLinearization := by
            have hfixed := horderOne_fixed_linearization sourceBase
            rw [hsource_forward] at hfixed
            simpa only [sourceLinearization, stableLinearization] using hfixed
          have hstableExpansion :
              stableOutput
                    (sourceBase + sourceIncrement,
                      ζ (sourceBase + sourceIncrement)) -
                  stableOutput (sourceBase, ζ sourceBase) =
                fderiv ℝ stableOutput (sourceBase, ζ sourceBase)
                    (sourceIncrement,
                      ζ (sourceBase + sourceIncrement) - ζ sourceBase) +
                  stableError := by
            dsimp only [stableError]
            abel
          have hone_eq : (1 : ℕ) = 1 := rfl
          have htargetDefect :
              rawTopDefect u s =
                stableOutput
                    (sourceBase + sourceIncrement,
                      ζ (sourceBase + sourceIncrement)) -
                  stableOutput (sourceBase, ζ sourceBase) -
                  s • derivativeValue u := by
            dsimp only [rawTopDefect]
            rw [horderOne_stable_endpoint_difference hone_eq u s]
            rw [hsource_endpoint]
          have hremainder_decomposition :
              rawTopDefect u s =
                principalOperator u sourceDefect + remainder := by
            rw [htargetDefect, hstableExpansion,
              hlinearizedGraphDirection, hfixedLinearization_source]
            dsimp only [remainder, inverseError, sourceIncrement]
            simp only [smul_eq_mul]
            rw [sub_smul, smul_smul]
            rw [sub_smul, sub_smul]
            abel
          have hstableError_bound :
              ‖stableError‖ ≤ (η / 2) * ‖s‖ := by
            have hstableSource := hstableGraphRemainder sourceBase
              sourceIncrement hsourceIncrement_small
            have hstableSource' :
                ‖stableError‖ ≤
                  (η / (2 * c)) * ‖sourceIncrement‖ := by
              simpa only [stableError] using hstableSource
            have hstableRate_nonneg : 0 ≤ η / (2 * c) := by
              positivity
            calc
              ‖stableError‖ ≤
                  (η / (2 * c)) * ‖sourceIncrement‖ := hstableSource'
              _ ≤ (η / (2 * c)) * (c * ‖s‖) :=
                mul_le_mul_of_nonneg_left hsourceIncrement_norm
                  hstableRate_nonneg
              _ = (η / 2) * ‖s‖ := by
                field_simp [hc_pos.ne']
          have hinverseError_bound :
              ‖inverseError‖ ≤
                (η / (2 * stableLinearizationBound)) * ‖s‖ := by
            simpa only [inverseError, sourceIncrement] using
              hinverseRemainder u s hs_inverse
          have htransportError_bound :
              ‖inverseError • sourceLinearization‖ ≤
                (η / 2) * ‖s‖ := by
            calc
              ‖inverseError • sourceLinearization‖ =
                  ‖inverseError‖ * ‖sourceLinearization‖ := by
                rw [norm_smul]
              _ ≤ (η / (2 * stableLinearizationBound) * ‖s‖) *
                  stableLinearizationBound := by
                apply mul_le_mul
                · exact hinverseError_bound
                · exact hstableLinearization_norm_le sourceBase
                · positivity
                · positivity
              _ = (η / 2) * ‖s‖ := by
                field_simp [hstableLinearizationBound_pos.ne']
          have hremainder_bound : ‖remainder‖ ≤ η * ‖s‖ := by
            calc
              ‖remainder‖ ≤ ‖stableError‖ +
                  ‖inverseError • sourceLinearization‖ := by
                dsimp only [remainder]
                exact norm_add_le _ _
              _ ≤ (η / 2) * ‖s‖ + (η / 2) * ‖s‖ :=
                add_le_add hstableError_bound htransportError_bound
              _ = η * ‖s‖ := by ring
          refine ⟨principalOperator u, remainder,
            hprincipalOperator_norm_le u, ?_, hremainder_bound⟩
          simpa only [sourceDefect] using hremainder_decomposition
        have hderivativeValue_norm_le (u : ℝ) :
            ‖derivativeValue u‖ ≤ (r.factorial : ℝ) * ‖a‖ := by
          have ha_apply : ‖a u oneTop‖ ≤ ‖a‖ := by
            calc
              ‖a u oneTop‖ ≤ ‖a u‖ * ∏ i : Fin r, ‖oneTop i‖ :=
                ContinuousMultilinearMap.le_opNorm (a u) oneTop
              _ = ‖a u‖ := by
                simp only [oneTop, norm_one, Finset.prod_const_one, mul_one]
              _ ≤ ‖a‖ := BoundedContinuousFunction.norm_coe_le_norm a u
          have hfactorial_nonneg : 0 ≤ (r.factorial : ℝ) := by
            positivity
          calc
            ‖derivativeValue u‖ = (r.factorial : ℝ) * ‖a u oneTop‖ := by
              simp only [derivativeValue, norm_smul,
                Real.norm_of_nonneg hfactorial_nonneg]
            _ ≤ (r.factorial : ℝ) * ‖a‖ :=
              mul_le_mul_of_nonneg_left ha_apply hfactorial_nonneg
        have hpredecessorNormBound_nonneg : 0 ≤ predecessorNormBound := by
          dsimp only [predecessorNormBound]
          positivity
        have hrawTopDefect_norm_le (u h : ℝ) :
            ‖rawTopDefect u h‖ ≤
              2 * predecessorNormBound + ‖h‖ * ((r.factorial : ℝ) * ‖a‖) := by
          have hpredecessor_sub :
              ‖predecessorValue (u + h) - predecessorValue u‖ ≤
                2 * predecessorNormBound := by
            calc
              ‖predecessorValue (u + h) - predecessorValue u‖ ≤
                  ‖predecessorValue (u + h)‖ + ‖predecessorValue u‖ :=
                norm_sub_le _ _
              _ ≤ predecessorNormBound + predecessorNormBound :=
                add_le_add (hpredecessor_norm_le _) (hpredecessor_norm_le _)
              _ = 2 * predecessorNormBound := by ring
          calc
            ‖rawTopDefect u h‖ ≤
                ‖predecessorValue (u + h) - predecessorValue u‖ +
                  ‖h • derivativeValue u‖ := norm_sub_le _ _
            _ ≤ 2 * predecessorNormBound +
                  ‖h‖ * ((r.factorial : ℝ) * ‖a‖) := by
              rw [norm_smul, Real.norm_eq_abs]
              exact add_le_add hpredecessor_sub
                (mul_le_mul_of_nonneg_left (hderivativeValue_norm_le u)
                  (abs_nonneg h))
        have hinverse_increment_norm_le (u s : ℝ) :
            ‖inverseCenter (u + s) - inverseCenter u‖ ≤ c * ‖s‖ := by
          calc
            ‖inverseCenter (u + s) - inverseCenter u‖ =
                dist (inverseCenter (u + s)) (inverseCenter u) := by
              rw [dist_eq_norm]
            _ ≤ (lower⁻¹ : ℝ) * dist (u + s) u :=
              (hcenter_inverse_lipschitz ζ).dist_le_mul _ _
            _ = c * ‖s‖ := by
              rw [dist_eq_norm, add_sub_cancel_left]
              rfl
        let defectRange (y : ℝ) : Set ℝ :=
          {z | ∃ u h : ℝ, ‖h‖ ≤ y ∧ z = ‖rawTopDefect u h‖}
        let defectEnvelope (y : ℝ) : ℝ := sSup (defectRange y)
        have htopScale_nonneg : 0 ≤ (r.factorial : ℝ) * ‖a‖ := by
          positivity
        have hdefectRange_mem (y z : ℝ) :
            z ∈ defectRange y ↔
              ∃ u h : ℝ, ‖h‖ ≤ y ∧ z = ‖rawTopDefect u h‖ := by
          rfl
        have hdefectEnvelope_eq (y : ℝ) :
            defectEnvelope y = sSup (defectRange y) := by
          rfl
        have hdefectRange_nonempty {y : ℝ} (hy : 0 ≤ y) :
            (defectRange y).Nonempty := by
          refine ⟨0, ?_⟩
          refine ⟨0, 0, ?_, ?_⟩
          · exact norm_zero.trans_le hy
          · rw [hrawTopDefect_zero, norm_zero]
        have hdefectRange_bdd {y : ℝ} (hy : 0 ≤ y) :
            BddAbove (defectRange y) := by
          refine ⟨2 * predecessorNormBound +
            y * ((r.factorial : ℝ) * ‖a‖), ?_⟩
          rintro z ⟨u, h, hh, rfl⟩
          exact (hrawTopDefect_norm_le u h).trans
            (add_le_add le_rfl
              (mul_le_mul_of_nonneg_right hh htopScale_nonneg))
        have hdefectEnvelope_nonneg {y : ℝ} (hy : 0 ≤ y) :
            0 ≤ defectEnvelope y := by
          apply le_csSup (hdefectRange_bdd hy)
          refine ⟨0, 0, ?_⟩
          refine ⟨?_, ?_⟩
          · exact norm_zero.trans_le hy
          · rw [hrawTopDefect_zero, norm_zero]
        have hdefectEnvelope_upper {y : ℝ} (hy : 0 ≤ y) :
            defectEnvelope y ≤
              2 * predecessorNormBound + y * ((r.factorial : ℝ) * ‖a‖) := by
          apply csSup_le (hdefectRange_nonempty hy)
          rintro z ⟨u, h, hh, rfl⟩
          exact (hrawTopDefect_norm_le u h).trans
            (add_le_add le_rfl
              (mul_le_mul_of_nonneg_right hh htopScale_nonneg))
        have hdefectEnvelope_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
            defectEnvelope x ≤ defectEnvelope y := by
          apply csSup_le (hdefectRange_nonempty hx)
          rintro z ⟨u, h, hh, rfl⟩
          apply le_csSup (hdefectRange_bdd (hx.trans hxy))
          exact ⟨u, h, hh.trans hxy, rfl⟩
        have hdefectEnvelope_bounded :
            ∃ δ > 0, ∃ M ≥ 0, ∀ y, 0 ≤ y → y < δ →
              defectEnvelope y ≤ M := by
          let M : ℝ :=
            2 * predecessorNormBound + (r.factorial : ℝ) * ‖a‖
          have hM_nonneg : 0 ≤ M := by
            dsimp only [M]
            have htwo_nonneg : (0 : ℝ) ≤ 2 := by
              norm_num
            exact add_nonneg
              (mul_nonneg htwo_nonneg hpredecessorNormBound_nonneg)
              htopScale_nonneg
          have hone_pos : (0 : ℝ) < 1 := by
            norm_num
          refine ⟨1, hone_pos, M, hM_nonneg, ?_⟩
          intro y hy hy_one
          calc
            defectEnvelope y ≤
                2 * predecessorNormBound +
                  y * ((r.factorial : ℝ) * ‖a‖) := hdefectEnvelope_upper hy
            _ ≤ 2 * predecessorNormBound +
                  (r.factorial : ℝ) * ‖a‖ := by
              have hscale :
                  y * ((r.factorial : ℝ) * ‖a‖) ≤
                    (r.factorial : ℝ) * ‖a‖ := by
                exact (mul_le_mul_of_nonneg_right hy_one.le htopScale_nonneg).trans_eq
                  (one_mul _)
              simpa [add_comm] using
                (add_le_add_left hscale (2 * predecessorNormBound))
            _ = M := rfl
        have hrawTopDefect_recurrence (η : ℝ) (hη : 0 < η) :
            ∃ δ > 0, ∀ u s : ℝ, s ≠ 0 → ‖s‖ < δ →
              ‖rawTopDefect u s‖ ≤
                p * ‖rawTopDefect (inverseCenter u)
                  (inverseCenter (u + s) - inverseCenter u)‖ + η * ‖s‖ := by
          obtain ⟨δ, hδ, hcertificate⟩ :=
            hpredecessor_affineCocycle_certificate η hη
          refine ⟨δ, hδ, ?_⟩
          intro u s hs hsδ
          obtain ⟨contracted, remainder, hcontracted, hdecomposition,
              hremainder⟩ :=
            hcertificate u s hs hsδ
          have hprincipal_norm :
              ‖contracted
                  (rawTopDefect (inverseCenter u)
                    (inverseCenter (u + s) - inverseCenter u))‖ ≤
                p * ‖rawTopDefect (inverseCenter u)
                  (inverseCenter (u + s) - inverseCenter u)‖ := by
            calc
              _ ≤ ‖contracted‖ *
                    ‖rawTopDefect (inverseCenter u)
                      (inverseCenter (u + s) - inverseCenter u)‖ :=
                contracted.le_opNorm _
              _ ≤ p * ‖rawTopDefect (inverseCenter u)
                    (inverseCenter (u + s) - inverseCenter u)‖ :=
                mul_le_mul_of_nonneg_right hcontracted
                  (norm_nonneg _)
          calc
            ‖rawTopDefect u s‖ =
                ‖contracted
                    (rawTopDefect (inverseCenter u)
                      (inverseCenter (u + s) - inverseCenter u)) +
                  remainder‖ :=
              congrArg norm hdecomposition
            _ ≤ ‖contracted
                    (rawTopDefect (inverseCenter u)
                      (inverseCenter (u + s) - inverseCenter u))‖ +
                  ‖remainder‖ :=
              norm_add_le _ _
            _ ≤ p * ‖rawTopDefect (inverseCenter u)
                    (inverseCenter (u + s) - inverseCenter u)‖ + η * ‖s‖ :=
              add_le_add hprincipal_norm hremainder
        have hdefectEnvelope_recurrence (η : ℝ) (hη : 0 < η) :
            ∃ δ > 0, ∀ y, 0 < y → y < δ →
              defectEnvelope y ≤ p * defectEnvelope (c * y) + η * y := by
          exact defectEnvelope_recurrence_of_rawRecurrence rawTopDefect
            inverseCenter p c η defectRange defectEnvelope hdefectRange_mem
            hdefectRange_nonempty hdefectRange_bdd hdefectEnvelope_eq
            hdefectEnvelope_nonneg hrawTopDefect_zero hη.le hp_nonneg hc_pos
            hinverse_increment_norm_le (hrawTopDefect_recurrence η hη)
        have hpc_lt : p * c < 1 := by
          rw [hp_mul_c]
          exact hq_real_lt
        have hrawTopDefect_le_envelope (u t : ℝ) :
            ‖rawTopDefect u t‖ ≤ defectEnvelope ‖t‖ := by
          apply le_csSup (hdefectRange_bdd (norm_nonneg t))
          exact ⟨u, t, le_rfl, rfl⟩
        have hrawDifference_sub_fixed_norm (t u : ℝ) (ht : t ≠ 0) :
            ‖sections t u - a u‖ =
              ‖(r.factorial : ℝ)⁻¹ • t⁻¹ • rawTopDefect u t‖ := by
          rw [hsections_distance t ht u]
          have hnormalized :
              (r.factorial : ℝ)⁻¹ • t⁻¹ • rawTopDefect u t =
                (r.factorial : ℝ)⁻¹ • t⁻¹ •
                    (predecessorValue (u + t) - predecessorValue u) -
                  a u oneTop := by
            dsimp only [rawTopDefect, derivativeValue]
            exact normalized_sub_factorial_smul r t ht
              (predecessorValue (u + t)) (predecessorValue u) (a u oneTop)
          rw [hnormalized]
        have hsection_dist_le (t : ℝ) (ht : t ≠ 0) :
            dist (sections t) a ≤
              ‖(r.factorial : ℝ)⁻¹‖ * ‖t⁻¹‖ * defectEnvelope ‖t‖ := by
          apply boundedContinuousFunction_dist_le_of_pointwise
          intro u
          simp only [dist_eq_norm]
          rw [hrawDifference_sub_fixed_norm t u ht, norm_smul, norm_smul]
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left (hrawTopDefect_le_envelope u t)
              (mul_nonneg (norm_nonneg ((r.factorial : ℝ)⁻¹))
                (norm_nonneg (t⁻¹)))
        exact tendsto_multilinearSection_of_radiusEnvelope_explicit
          sections a defectEnvelope ‖(r.factorial : ℝ)⁻¹‖ p c
          (norm_nonneg _) hdefectEnvelope_mono hp_nonneg hp_lt hc_pos hpc_lt
          hdefectEnvelope_bounded hdefectEnvelope_recurrence
          hsection_dist_le hsections_zero
      exact ⟨sections, hsections_tendsto, hsecant⟩
    obtain ⟨sections, hsections, hsecant⟩ := hpredecessor_secant_certificate
    have hpredecessor_hasDeriv : ∀ u,
        HasDerivAt predecessorValue (derivativeValue u) u := by
      intro u
      simpa only [derivativeValue, oneTop] using
        hasDerivAt_of_factorial_section_secant predecessorValue sections a oneTop
          hsections hsecant u
    -- Pointwise derivative witnesses give differentiability and identify the
    -- derivative function; continuity of that field then closes `C^1`.
    have hpredecessor_differentiable : Differentiable ℝ predecessorValue := by
      intro u
      exact (hpredecessor_hasDeriv u).differentiableAt
    have hpredecessor_deriv : deriv predecessorValue = derivativeValue := by
      funext u
      exact (hpredecessor_hasDeriv u).deriv
    have hpredecessor_contDiff : ContDiff ℝ 1 predecessorValue := by
      rw [contDiff_one_iff_deriv]
      exact ⟨hpredecessor_differentiable,
        hpredecessor_deriv ▸ hderivativeValue_continuous⟩
    simpa only [predecessorValue] using hpredecessor_contDiff
  -- The scalar-source successor criterion now closes the induction step
  -- without transporting derivatives through multilinear-map instances.
  have hζ_prev_nat : ContDiff ℝ (r - 1 : ℕ) (ζ : ℝ → X) := by
    have horder_prev : (r : WithTop ℕ∞) - 1 =
        ((r - 1 : ℕ) : WithTop ℕ∞) := by
      calc
        (r : WithTop ℕ∞) - 1 =
            (((r : ℕ∞) - (1 : ℕ∞) : ℕ∞) : WithTop ℕ∞) :=
          (WithTop.coe_sub (a := (r : ℕ∞)) (b := (1 : ℕ∞))).symm
        _ = (((r - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) :=
          congrArg (fun n : ℕ∞ ↦ (n : WithTop ℕ∞)) (ENat.coe_sub r 1).symm
    rw [horder_prev] at hζ_prev
    exact hζ_prev
  have hζ_succ : ContDiff ℝ (r - 1 + 1 : ℕ) (ζ : ℝ → X) :=
    contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mpr
      ⟨hζ_prev_nat, hpredecessor_contDiff_one⟩
  simpa only [Nat.sub_add_cancel hr_pos] using hζ_succ

/-- A fixed small Lipschitz graph is `C^ν` when the cutoff graph transform satisfies
the bunching inequality at every positive order through `ν`. -/
theorem fixedPoint_contDiff (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hχ_smooth : ContDiff ℝ ν χ) (hχ_support : HasCompactSupport χ)
    (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_linearRate : linearRate < 1)
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_center_fiber : ∀ u : ℝ, ∀ z w : X,
      |(LocalCutoff.remainder χ ρ N (u, z)).1 -
          (LocalCutoff.remainder χ ρ N (u, w)).1| ≤
        (centerFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (h_rate : rate lower linearRate stableCenter stableFiber centerFiber slope < 1)
    (h_bunching : ∀ r, 1 ≤ r → r ≤ ν →
      rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r < 1)
    (ζ : SmallLipschitzGraph X radius slope)
    (hζ_fixed : map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz
      h_radius h_slope ζ = ζ) :
    ContDiff ℝ ν ζ := by
  have hall : ∀ r : ℕ, r ≤ ν → ContDiff ℝ r ζ := by
    intro r hrν
    induction r with
    | zero => exact contDiff_zero.mpr ζ.val.continuous
    | succ r hregular =>
        have hr_pos : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
        have hr_le : r ≤ ν := (Nat.le_succ r).trans hrν
        have horder : (r : WithTop ENat) + 1 - 1 = (r : WithTop ENat) := by
          norm_cast
        have hprevious : ContDiff ℝ ((r + 1) - 1) ζ := by
          rw [horder]
          exact hregular hr_le
        exact contDiff_succ_of_fixedPoint (r + 1) ν χ ρ L N lower linearRate
          stableBound stableCenter stableFiber centerFiber hν hr_pos hrν hχ_smooth
          hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL
          h_linearRate h_stable_bound h_stable_lipschitz h_center_fiber h_radius h_slope
          h_rate (h_bunching (r + 1) hr_pos hrν) ζ hprevious hζ_fixed
  exact hall ν le_rfl

end LocalCutoff.GraphTransform
